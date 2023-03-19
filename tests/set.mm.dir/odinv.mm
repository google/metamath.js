include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "cgcd.mm"
include "co.mm"
include "cmg.mm"
include "cmul.mm"
include "cz.mm"
include "wceq.mm"
include "neg1z.mm"
include "eqid.mm"
include "odmulg.mm"
include "mp3an3.mm"
include "cn0.mm"
include "odcl.mm"
include "adantl.mm"
include "nn0zd.mm"
include "gcdcom.mm"
include "sylancr.mm"
include "1z.mm"
include "gcdneg.mm"
include "sylancl.mm"
include "gcd1.mm"
include "syl.mm"
include "3eqtrd.mm"
include "mulgm1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "grpinvcl.mm"
include "nn0cnd.mm"
include "mulid2d.mm"
include "3eqtrrd.mm"

theorem odinv
  let cA: class A
  let cG: class G
  let cI: class I
  let cO: class O
  let cX: class X
  assume odinv.1: |- O = ( od ` G )
  assume odinv.2: |- I = ( invg ` G )
  assume odinv.3: |- X = ( Base ` G )


  assert |- ( ( G e. Grp /\ A e. X ) -> ( O ` ( I ` A ) ) = ( O ` A ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    cO
    cfv
    #
    c1
    cneg
    #
    @3
    cgcd
    co
    #
    @4
    cA
    cG
    cmg
    cfv
    #
    co
    #
    cO
    cfv
    #
    cmul
    co
    #
    c1
    cA
    cI
    cfv
    #
    cO
    cfv
    #
    cmul
    co
    @11
    @0
    @1
    @4
    cz
    wcel
    #
    @3
    @9
    wceq
    neg1z
    cA
    @6
    cG
    @4
    cO
    cX
    odinv.3
    odinv.1
    @6
    eqid
    #
    odmulg
    mp3an3
    @2
    @5
    c1
    @8
    @11
    cmul
    @2
    @5
    @3
    @4
    cgcd
    co
    #
    @3
    c1
    cgcd
    co
    #
    c1
    @2
    @12
    @3
    cz
    wcel
    #
    @5
    @14
    wceq
    neg1z
    @2
    @3
    @1
    @3
    cn0
    wcel
    @0
    cA
    cG
    cO
    cX
    odinv.3
    odinv.1
    odcl
    adantl
    nn0zd
    #
    @4
    @3
    gcdcom
    sylancr
    @2
    @16
    c1
    cz
    wcel
    @14
    @15
    wceq
    @17
    1z
    @3
    c1
    gcdneg
    sylancl
    @2
    @16
    @15
    c1
    wceq
    @17
    @3
    gcd1
    syl
    3eqtrd
    @2
    @7
    @10
    cO
    cX
    @6
    cG
    cI
    cA
    odinv.3
    @13
    odinv.2
    mulgm1
    fveq2d
    oveq12d
    @2
    @11
    @2
    @11
    @2
    @10
    cX
    wcel
    @11
    cn0
    wcel
    cX
    cG
    cI
    cA
    odinv.3
    odinv.2
    grpinvcl
    @10
    cG
    cO
    cX
    odinv.3
    odinv.1
    odcl
    syl
    nn0cnd
    mulid2d
    3eqtrrd
end
