include "cnghm.mm"
include "co.mm"
include "wcel.mm"
include "w3a.mm"
include "csg.mm"
include "cfv.mm"
include "cnm.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "simp1.mm"
include "cgrp.mm"
include "cngp.mm"
include "nghmrcl1.mm"
include "ngpgrp.mm"
include "syl.mm"
include "eqid.mm"
include "grpsubcl.mm"
include "syl3an1.mm"
include "nmoi.mm"
include "syl2anc.mm"
include "cbs.mm"
include "wceq.mm"
include "nghmrcl2.mm"
include "3ad2ant1.mm"
include "cghm.mm"
include "wf.mm"
include "nghmghm.mm"
include "ghmf.mm"
include "simp2.mm"
include "ffvelrnd.mm"
include "simp3.mm"
include "ngpds.mm"
include "syl3anc.mm"
include "ghmsub.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "3brtr4d.mm"

theorem nmods
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cF: class F
  let cN: class N
  let cV: class V
  assume nmods.n: |- N = ( S normOp T )
  assume nmods.v: |- V = ( Base ` S )
  assume nmods.c: |- C = ( dist ` S )
  assume nmods.d: |- D = ( dist ` T )


  assert |- ( ( F e. ( S NGHom T ) /\ A e. V /\ B e. V ) -> ( ( F ` A ) D ( F ` B ) ) <_ ( ( N ` F ) x. ( A C B ) ) )

  proof
    cF
    cS
    cT
    cnghm
    co
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    w3a
    #
    cA
    cB
    cS
    csg
    cfv
    #
    co
    #
    cF
    cfv
    #
    cT
    cnm
    cfv
    #
    cfv
    #
    cF
    cN
    cfv
    #
    @5
    cS
    cnm
    cfv
    #
    cfv
    #
    cmul
    co
    #
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    cD
    co
    #
    @9
    cA
    cB
    cC
    co
    #
    cmul
    co
    cle
    @3
    @0
    @5
    cV
    wcel
    #
    @8
    @12
    cle
    wbr
    @0
    @1
    @2
    simp1
    @0
    cS
    cgrp
    wcel
    #
    @1
    @2
    @17
    @0
    cS
    cngp
    wcel
    #
    @18
    cS
    cT
    cF
    nghmrcl1
    #
    cS
    ngpgrp
    syl
    cV
    cS
    @4
    cA
    cB
    nmods.v
    @4
    eqid
    #
    grpsubcl
    syl3an1
    cS
    cT
    cF
    @10
    @7
    cN
    cV
    @5
    nmods.n
    nmods.v
    @10
    eqid
    #
    @7
    eqid
    #
    nmoi
    syl2anc
    @3
    @15
    @13
    @14
    cT
    csg
    cfv
    #
    co
    #
    @7
    cfv
    #
    @8
    @3
    cT
    cngp
    wcel
    #
    @13
    cT
    cbs
    cfv
    #
    wcel
    @14
    @28
    wcel
    @15
    @26
    wceq
    @0
    @1
    @27
    @2
    cS
    cT
    cF
    nghmrcl2
    3ad2ant1
    @3
    cV
    @28
    cA
    cF
    @3
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cV
    @28
    cF
    wf
    @0
    @1
    @29
    @2
    cS
    cT
    cF
    nghmghm
    #
    3ad2ant1
    cS
    cT
    cF
    cV
    @28
    nmods.v
    @28
    eqid
    #
    ghmf
    syl
    #
    @0
    @1
    @2
    simp2
    ffvelrnd
    @3
    cV
    @28
    cB
    cF
    @32
    @0
    @1
    @2
    simp3
    ffvelrnd
    @13
    @14
    cD
    cT
    @24
    @7
    @28
    @23
    @31
    @24
    eqid
    #
    nmods.d
    ngpds
    syl3anc
    @3
    @6
    @25
    @7
    @0
    @29
    @1
    @2
    @6
    @25
    wceq
    @30
    cV
    cS
    cT
    cA
    cF
    @4
    @24
    cB
    nmods.v
    @21
    @33
    ghmsub
    syl3an1
    fveq2d
    eqtr4d
    @3
    @16
    @11
    @9
    cmul
    @0
    @19
    @1
    @2
    @16
    @11
    wceq
    @20
    cA
    cB
    cC
    cS
    @4
    @10
    cV
    @22
    nmods.v
    @21
    nmods.c
    ngpds
    syl3an1
    oveq2d
    3brtr4d
end
