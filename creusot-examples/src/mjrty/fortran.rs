
/// Compile Fortran to Rust!
macro_rules! fortran {
    (@compile $r:lifetime {$($stack:tt)*} {$($stmts:stmt)*} $var:ident = $($rest:tt)*) => {
        fortran! { @assign $r $var
            { $($stack)* }
            { $($stmts)* }
            $($rest)*
        }
    };
    (@compile $r:lifetime {$($stack:tt)*} break {$($stmts:stmt)*} $lbl:lifetime $($rest:tt)*) => {
        fortran! { @compile $r
            { $($stack)* }
            { fortran! { @retokenize $lbl: loop { $($stmts)* } } }
            $($rest)*
        }
    };
    (@compile $r:lifetime {$($stack:tt)*} {$($stmts:stmt)*} $lbl:lifetime $($rest:tt)*) => {
        fortran! { @compile $r
            { $($stack)* }
            { fortran! { @retokenize $lbl: loop { $($stmts)* break; } } }
            $($rest)*
        }
    };
    (@compile $r:lifetime {$($stack:tt)*} {$($stmts:stmt)*} $(#[$invariant:meta])* DO $var:ident = $i:literal, $n:ident $($rest:tt)* ) => {
        fortran! { @compile $r
            { { $($stmts)* } $(#[$invariant])* DO $var = $i , $n $($stack)* }
            {}
            $($rest)*
        }
    };
    (@compile $r:lifetime {$($stack:tt)*} {$($stmts:stmt)*} GOTO $lbl:lifetime $($rest:tt)*) => {
        fortran! { @compile $r
            { $($stack)* }
            break
            { $($stmts)* break $lbl; }
            $($rest)*
        }
    };
    (@compile $r:lifetime {$($stack:tt)*} {$($stmts:stmt)*} IF (($($cond:tt)*)) GOTO $lbl:lifetime $($rest:tt)*) => {
        fortran! { @compile $r
            { $($stack)* }
            { $($stmts)* if fortran!(@expr $($cond)*) { break $lbl; } }
            $($rest)*
        }
    };
    (@compile $r:lifetime {$($stack:tt)*} {$($stmts:stmt)*} IF (($($cond:tt)*)) RETURN $($rest:tt)*) => {
        fortran! { @compile $r
            { $($stack)* }
            { $($stmts)* if fortran!(@expr $($cond)*) { break $r } }
            $($rest)*
        }
    };
    (@compile $r:lifetime {{$($stmts0:stmt)*} $(#[$invariant:meta])* DO $var:ident = $i:literal, $n:ident $($stack:tt)*} {$($stmts:stmt)*} CONTINUE $($rest:tt)* ) => {
        fortran! { @compile $r
            { $($stack)* }
            {
                $($stmts0)*
                $var = $i;
                $(#[cfg_attr(creusot, $invariant)])*
                while $var <= $n {
                    $($stmts)*
                    $var += 1;
                }
            }
            $($rest)*
        }
    };
    (@compile $r:lifetime {} {$($stmts:stmt)*} RETURN END) => {
        $($stmts)*
    };
    (@compile $r:lifetime {$($stack:tt)*} {$($stmts:stmt)*} RETURN $($rest:tt)*) => {
        fortran! { @compile $r
            { $($stack)* }
            { $($stmts)* break $r; }
            $($rest)*
        }
    };
    (@compile $r:lifetime {} {$($stmts:stmt)*} END ) => { $($stmts)* };
    (@assign $r:lifetime $v:ident {$($stack:tt)*} {$($stmts:stmt)*} $n:literal $($rest:tt)*) => {
        fortran! { @compile $r
            { $($stack)* }
            { $($stmts)* $v = $n; }
            $($rest)*
        }
    };
    (@assign $r:lifetime $v:ident {$($stack:tt)*} {$($stmts:stmt)*} $a:ident ($($e:tt)*) $($rest:tt)*) => {
        fortran! { @compile $r
            { $($stack)* }
            { $($stmts)* $v = $a.get(fortran!(@expr $($e)*)-1); }
            $($rest)*
        }
    };
    (@assign $r:lifetime $v:ident {$($stack:tt)*} {$($stmts:stmt)*} ($($e:tt)*) $($rest:tt)*) => {
        fortran! { @compile $r
            { $($stack)* }
            { $($stmts)* $v = fortran!(@expr $($e)*); }
            $($rest)*
        }
    };
    (@assign $r:lifetime $v:ident {$($stack:tt)*} {$($stmts:stmt)*} .TRUE. $($rest:tt)*) => {
        fortran! { @compile $r
            { $($stack)* }
            { $($stmts)* $v = true; }
            $($rest)*
        }
    };
    (@assign $r:lifetime $v:ident {$($stack:tt)*} {$($stmts:stmt)*} .FALSE. $($rest:tt)*) => {
        fortran! { @compile $r
            { $($stack)* }
            { $($stmts)* $v = false; }
            $($rest)*
        }
    };
    // Hack to work around a parser issue when the `$lbl` token is a `lifetime`.
    (@retokenize $lbl:tt: loop { $($stmts:stmt)* }) => { $lbl: loop { $($stmts)* } };
    (@expr $v:ident ($($e:tt)*)) => { $v.get(fortran!(@expr $($e)*)-1) };
    (@expr $v:ident) => { $v };
    (@expr $n:literal) => { $n };
    (@expr .FALSE.) => { false };
    (@expr .TRUE.) => { true };
    (@expr ($($rest:tt)*)) => { fortran!(@expr $($rest)*) };
    (@expr $v:ident .EQ. $($rest:tt)*) => { ($v == fortran!(@expr $($rest)*)) };
    (@expr $v:ident .NE. $($rest:tt)* ) => { ($v != fortran!(@expr $($rest)*)) };
    (@expr $v:ident .GT. $($rest:tt)* ) => { ($v > fortran!(@expr $($rest)*)) };
    (@expr $v:ident / $($rest:tt)* ) => { ($v / fortran!(@expr $($rest)*)) };
    (@expr $v:ident + $($rest:tt)* ) => { ($v + fortran!(@expr $($rest)*)) };
    (@expr $v:ident - $($rest:tt)* ) => { ($v - fortran!(@expr $($rest)*)) };
    (@ $($rest:tt)*) => { compile_error!() };
    ($($rest:tt)*) => {
        #[allow(redundant_semicolons)]
        'RETURN: loop {
            fortran! { @compile 'RETURN {} {} $($rest)* }
            break;
        }
    }
}

pub(crate) use fortran;
