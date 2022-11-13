      $c wff |- t p q - C DND DF P $.
      $v x y z $.
      wx $f wff x $.
      wy $f wff y $.
      wz $f wff z $.

      $( 1 is a wff $)
      w0 $a wff - $.          

      $( n is a wff $)
      w1 $a wff x - $.

      $( 2 is a wff $)
      t0 $p wff - - $= w0 w1 $.

      $( 3 is a wff $)
      t1 $p wff - - - $= w0 w1 w1 $.

      $( x * 1 = x $)
      ax0 $a |- x t - q x $.

      $( 1 * 1 = 1 $)
      t2 $p |- - t - q - $= w0 ax0 $.

      $( 2 * 1 = 2 $)
      t3 $p |- - - t - q - - $= t0 ax0 $.

      $( if x * y = z then x * (y + 1) = (z + x) $)
      ${
        ax1.1 $e |- x t y q z $.
        ax1 $a |- x t y - q z x $.
      $}

      $( since 1 * 1 = 1 then 1 * 2 = 2 $)
      t4 $p |- - t - - q - - $= 
        w0             $( x = -, i.e. 1 $)
        w0             $( y = -, i.e. 1 $)
        w0             $( z = -, i.e. 1 $)
        w0 ax0         $( |- - t - q - -, i.e. 1 * 1 = 1 $)
        ax1            $( |- - t - - q - - , i.e. 1 * 2 = 2 $)
      $.

      $( since 2 * 1 = 2 then 2 * 2 = 4 $)
      t5 $p |- - - t - - q - - - - $= 
        w0 w1          $( x = - -, i.e. 2 $)
        w0             $( y = -, i.e. 1 $)
        w0 w1          $( z = - -, i.e. 2 $)
        t3             $( |- - t - q - -, i.e. 2 * 1 = 2 $)
        ax1            $( |- - t - - q - - - -, i.e. 2 * 2 = 4 $)
      $.

      $( since 2 * 2 = 4 then 2 * 3 = 6 $)
      t6 $p |- - - t - - - q - - - - - - $= 
        w0 w1          $( x = - -, i.e. 2 $)
        w0 w1          $( y = - -, i.e. 2 $)
        w0 w1 w1 w1    $( z = - - - -, i.e. 4 $)
        t5             $( |- - t - - q - - - -, i.e. 2 * 2 = 4 $)
        ax1            $( |- - - t - - - q - - - - - -, i.e. 2 * 3 = 6 $)
      $.
      
      $( If Z is a product of two numbers (greater than one), Z is composite $)
      $( if (x + 1) * (y + 1) = z then C z $)
      ${
        ax2.1 $e |- x - t y - q z $.
        ax2 $a |- C z $.
      $}

      $( Since (1 + 1) * (1 + 1) = 4 then 4 is a product of two numbers 
         greater than 1, and hence, composite  $)
      t7 $p |- C - - - - $=
        w0             $( x = -, i.e. 1 $)
        w0             $( y = -, i.e. 1 $)
        w0 w1 w1 w1    $( z = - - - - -, i.e. 4 $)
        t5             $( |- - t - - q - - - -, i.e. 2 * 2 = 4 $)
        ax2            $( |- C - - - -, i.e. 4 is composite $)
      $.

      $( Since (1 + 1) * (2 + 1) = 6 then 6 is a product of two numbers 
         greater than 1, and hence, composite  $)
      t7 $p |- C - - - - - - $=
        w0                   $( x = -, i.e. 1 $)
        w0 w1                $( y = - -, i.e. 2 $)
        w0 w1 w1 w1 w1 w1    $( z = - - - - - - -, i.e. 6 $)
        t6                   $( |- - t - - q - - - -, i.e. 2 * 3 = 6 $)
        ax2                  $( |- C - - - - - -, i.e. 6 is composite $)
      $.

      $( Every number does not divide a smaller number $)
      $( x y DND x $)
      ax3 $a |- x y DND x $.

      $( 5 does not divide 2 $)
      t8 $p |- - - - - - DND - - $=
        w0 w1          $( x = - -, i.e. 2 $)
        w0 w1 w1       $( y = - - -, i.e. 3 $)
        ax3            $( |- - - - - - DND - -, i.e. "5 does not divide 2" is a wff $)
      $.

      $( if x DND y then x DND x y $)
      ${
        ax4.1 $e |- x DND y  $.
        ax4 $a |- x DND x y $.
      $}

      $( Since 5 DND 2, then 5 DND 7 $)
      t9 $p |- - - - - - DND - - - - - - - $=
        w0 w1 w1 w1 w1           $( x = - - - - -, i.e. 5 $)
        w0 w1                    $( y = - -, i.e. 2 $)
        t8                       $( |- - - - - - DND - -, i.e. 5 does not divide 2 $)
        ax4                      $( |- - - - - - DND - - - - - - -, i.e. 5 does not divide 7 $)
      $.

      $( Since 5 DND 7, then 5 DND 12 $)
      t10 $p |- - - - - - DND - - - - - - - - - - - - $=
        w0 w1 w1 w1 w1           $( x = - - - - -, i.e. 5 $)
        w0 w1 w1 w1 w1 w1 w1     $( y = - - - - - - -, i.e. 7 $)
        t9                       $( |- - - - - - DND - - - - - - -, i.e. 5 does not divide 7 $)
        ax4                      $( |- - - - - - DND - - - - - - - - - - - -, i.e. 5 does not divide 12 $)
      $.

      $( if - - DND z then z DF - - $)
      $( DF = "divisor free up to n" $)
      ${
        ax5.1 $e |- - - DND z  $.
        ax5 $a |- z DF - - $.
      $}

      $( if z DF x and x - DND z then z DF x - $)
      ${
        ax6.1 $e |- z DF x  $.
        ax6.2 $e |- x - DND z  $.
        ax6 $a |- z DF x - $.
      $}

      $( if z - DF z then P z -  $)
      ${
        ax7.1 $e |- z - DF z  $.
        ax7 $a |- P z - $.
      $}

      ax8 $a |- P - - $.

      $( 2 does not divide 1 $)
      $( Since 2 does not divide 1, 2 does not divide 3 $)
      $( Since 2 does not divide 3 then 3 is dividor free up to 2 $)
      $( Since 3 is divisor free up to 2, then 3 is prime $)
      t11 $p |- P - - - $=
        w0 w1          $( z = - -, i.e. 2 $)
          w0 w1 w1       $( z = - - -, i.e. 3 $)
            w0 w1          $( x = - -, i.e. 2 $)
            w0             $( y = -, i.e. 1 $)
              w0             $( x = -, i.e. 1 $)
              w0             $( y = -, i.e. 1 $)
              ax3            $( |- - - DND -, i.e. 2 does not divide 1 $)
            ax4            $( |- - - DND - - -, i.e. 2 does not divide 3 $)
          ax5            $( |- - - - DF - - $)
        ax7            $( |- P - - - $)
      $.
