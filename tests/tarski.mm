$( propositional logic $)

$( propositional logic syntax $)
$c wff $.

$( propositional logic symbols $)
$c ~ |- -> ( ) && || $.

$v p q r $.

wp $f wff p $.
wq $f wff q $.
wr $f wff r $.

$( if x is a wff so is ~ x $)
${
  $v x $.
  wx $f wff x $.
  wnot $a wff ~ x $.
$}

$( ~ p is a wff $)
$( x y = z w is a wff $)
wnotp $p wff ~ p $= wp wnot $.

$( if x and y are wffs so is ( x -> y ) $)
${
  $v x y $.
  wx $f wff x $.
  wy $f wff y $.
  wi $a wff ( x -> y ) $.
$}

$( modus ponens $)
${
  $v x y $.
  wx $f wff x $.
  wy $f wff y $.
  min $e |- x $.
  maj $e |- ( x -> y ) $.
  mp $a |- y $.
$}

$( simplification $)
${
  $v x y $.
  wx $f wff x $.
  wy $f wff y $.
  ax-1 $a |- ( x -> ( y -> x ) ) $.
$}

$( frege: distribution $)
${
  $v x y z $.
  wx $f wff x $.
  wy $f wff y $.
  wy $f wff z $.
  ax-2 $a |- ( ( x -> ( y -> z ) ) -> ( ( x -> y ) -> ( x -> z ) ) ) $.
$}

$(
  tranposition
  If there are not clouds in the sky, is not raining.
  If it is raining, there are clouds in the sky.
$)
${
  $v x y $.
  wx $f wff x $.
  wy $f wff y $.
  ax-3 $a |- ( ( ~ x -> ~ y ) -> ( y -> x )) $.
$}

$( declare first order logic symbols $)
$c E. A. $.

$( declare geometry constants $)
$c Point B = $.

$( x y z are well-formed formulas variables $)
$v x y z w u v a b $.
wx $f Point x $.
wy $f Point y $.
wz $f Point z $.
ww $f Point w $.
wu $f Point u $.
wv $f Point v $.
wa $f Point a $.
wb $f Point b $.

$( if x and y are Points then x y is a wff $)
${
  wffs.1 $f Point x $.
  wffs.2 $f Point y $.
  wffs $a wff x y $.
$}

$( if x, y and z are Points then B x y z is a wff $)
${
  wffb.1 $f Point x $.
  wffb.2 $f Point y $.
  wffb.3 $f Point z $.
  wffb $a wff B x y z $.
$}

$( if x, y, z and w are Point then x y = z w is a wff $)
${
  wffc.1 $f Point x $.
  wffc.2 $f Point y $.
  wffc.3 $f Point z $.
  wffc.4 $f Point w $.
  wffc $a wff x y = z w $.
$}

$( a b is a wff $)
wab $p wff a b $= wa wb wffs $.

$( x y is a wff $)
wxy $p wff x y $= wx wy wffs $.

$( y x is a wff $)
wyx $p wff y x $= wy wx wffs $.

$( B x y z is a wff $)
wxyz $p wff B x y z $= wx wy wz wffb $.

$( x y = z w is a wff $)
wxyzw $p wff x y = z w $= wx wy wz ww wffc $.

$( Reflexivity of Congruence $)
${
  ax-cref.1 $f Point x $.
  ax-cref.2 $f Point y $.
  ax-cref $a |- x y = y x $.
$}

$( Identity of Congruence $)
${
  ax-cid.1 $f Point x $.
  ax-cid.2 $f Point y $.
  ax-cid.3 $f Point z $.
  ax-cid $a |- x y = z z -> x = y $.
$}

$( Transitivity of Congruence $)
${
  ax-ctr.1 $f Point x $.
  ax-ctr.2 $f Point y $.
  ax-ctr.3 $f Point z $.
  ax-ctr.3 $f Point u $.
  ax-ctr.4 $f Point v $.
  ax-ctr $a |- ( x y = z u && x y = v w ) -> z u = v w $.
$}

$( Identity of Betweenness $)
${
  ax-bid.1 $f Point x $.
  ax-bid.2 $f Point y $.
  ax-bid $a |- B x y x -> x = y $.
$}

$( Pasch $)
${
  ax-pasch.1 $f Point x $.
  ax-pasch.2 $f Point y $.
  ax-pasch.3 $f Point z $.
  ax-pasch.4 $f Point u $.
  ax-pasch.5 $f Point v $.
  ax-pasch $a |- ( B x u z && B y v z ) -> E. a ( B u a y && B v a x ) $.
$}
