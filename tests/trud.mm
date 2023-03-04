      $( Declare the primitive constant symbols for lambda calculus. $)
      $c var $.   $( Typecode for variables (syntax) $)
      $c type $.  $( Typecode for types (syntax) $)
      $c term $.  $( Typecode for terms (syntax) $)
      $c |- $.    $( Typecode for theorems (logical) $)
      $c : $.     $( Typehood indicator $)
      $c . $.     $( Separator $)
      $c |= $.    $( Context separator $)
      $c bool $.     $( Boolean type $)
      $c ind $.   $( 'Individual' type $)
      $c -> $.    $( Function type $)
      $c ( $.     $( Open parenthesis $)
      $c ) $.     $( Close parenthesis $)
      $c , $.     $( Context comma $)
      $c \\ $.     $( Lambda expression $)
      $c = $.     $( Equality term $)
      $c T. $.    $( Truth term $)
      $c [ $.     $( Infix operator $)
      $c ] $.     $( Infix operator $)

      $v x y z f g p q $.  $( Bound variables $)
      $v A B C F R S T $.  $( Term variables $)

      $( Let variable A be a term. $)
      ta $f term A $.
      $( Let variable R be a term. $)
      tr $f term R $.
      $( Let variable S be a term. $)
      ts $f term S $.
      $( Let variable T be a term. $)
      tt $f term T $.

      $( Truth term. $)
      kt $a term T. $.

      ${
        ax-syl.1 $e |- R |= S $.
        ax-syl.2 $e |- S |= T $.
        $( Syllogism inference. $)
        ax-syl $a |- R |= T $.

        $( Syllogism inference. $)
        syl $p |- R |= T $=
          ( ax-syl ) ABCDEF $.
          $( [8-Oct-2014] $)
      $}

      ${
        ax-trud.1 $e |- R : bool $.
        $( Deduction form of ~ tru . $)
        ax-trud $a |- R |= T. $.

        $( Deduction form of ~ tru . $)
        trud $p |- R |= T. $=
          ( ax-trud ) ABC $.
          $( [7-Oct-2014] $)

        ax-a1i.2 $e |- T. |= A $.

        $( Change an empty context into any context. $)
        a1i $p |- R |= A $=
          ( kt ax-trud syl ) BEABCFDG $.
          $( [7-Oct-2014] $)

      $}
