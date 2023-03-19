include "cngp.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cr.mm"
include "nmcl.mm"
include "3adant3.mm"
include "3adant2.mm"
include "resubcld.mm"
include "recnd.mm"
include "abscld.mm"
include "simp1.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "grpsubcl.mm"
include "syl3an1.mm"
include "syl2anc.mm"
include "leabsd.mm"
include "nmrtri.mm"
include "letrd.mm"

theorem nm2dif
  let cA: class A
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  assume nmf.x: |- X = ( Base ` G )
  assume nmf.n: |- N = ( norm ` G )
  assume nmmtri.m: |- .- = ( -g ` G )


  assert |- ( ( G e. NrmGrp /\ A e. X /\ B e. X ) -> ( ( N ` A ) - ( N ` B ) ) <_ ( N ` ( A .- B ) ) )

  proof
    cG
    cngp
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cN
    cfv
    #
    cB
    cN
    cfv
    #
    cmin
    co
    #
    @6
    cabs
    cfv
    cA
    cB
    c.mi
    co
    #
    cN
    cfv
    #
    @3
    @4
    @5
    @0
    @1
    @4
    cr
    wcel
    @2
    cA
    cG
    cN
    cX
    nmf.x
    nmf.n
    nmcl
    3adant3
    @0
    @2
    @5
    cr
    wcel
    @1
    cB
    cG
    cN
    cX
    nmf.x
    nmf.n
    nmcl
    3adant2
    resubcld
    #
    @3
    @6
    @3
    @6
    @9
    recnd
    abscld
    @3
    @0
    @7
    cX
    wcel
    #
    @8
    cr
    wcel
    @0
    @1
    @2
    simp1
    @0
    cG
    cgrp
    wcel
    @1
    @2
    @10
    cG
    ngpgrp
    cX
    cG
    c.mi
    cA
    cB
    nmf.x
    nmmtri.m
    grpsubcl
    syl3an1
    @7
    cG
    cN
    cX
    nmf.x
    nmf.n
    nmcl
    syl2anc
    @3
    @6
    @9
    leabsd
    cA
    cB
    cG
    c.mi
    cN
    cX
    nmf.x
    nmf.n
    nmmtri.m
    nmrtri
    letrd
end
