include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "cmarrep.mm"
include "co.mm"
include "csubma.mm"
include "csn.mm"
include "cdif.mm"
include "cmdat.mm"
include "cmulr.mm"
include "crg.mm"
include "wceq.mm"
include "crngring.mm"
include "anim2i.mm"
include "ancomd.mm"
include "3adant3.mm"
include "adantr.mm"
include "simp3.mm"
include "anim1i.mm"
include "cur.mm"
include "cmat.mm"
include "fveq2i.mm"
include "1marepvmarrepid.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "a1i.mm"
include "fveq1d.mm"
include "cbs.mm"
include "simpl2.mm"
include "cmatrepV.mm"
include "eqcomi.mm"
include "eqid.mm"
include "ma1repvcl.mm"
include "syl5eqel.mm"
include "wi.mm"
include "cmap.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "ex.mm"
include "syl.mm"
include "eleq2s.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "smadiadetr.mm"
include "syl22anc.mm"
include "eqtrd.mm"
include "1marepvsma1.mm"
include "oveq2d.mm"
include "diffi.mm"
include "mdet1.mm"
include "3ad2ant2.mm"
include "ringridm.mm"
include "3eqtrd.mm"

theorem cramerimplem1
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cE: class E
  let cI: class I
  let cN: class N
  let cV: class V
  let cZ: class Z
  assume cramerimplem1.a: |- A = ( N Mat R )
  assume cramerimplem1.b: |- B = ( Base ` A )
  assume cramerimplem1.v: |- V = ( ( Base ` R ) ^m N )
  assume cramerimplem1.e: |- E = ( ( ( 1r ` A ) ( N matRepV R ) Z ) ` I )
  assume cramerimplem1.d: |- D = ( N maDet R )


  assert |- ( ( ( N e. Fin /\ R e. CRing /\ I e. N ) /\ Z e. V ) -> ( D ` E ) = ( Z ` I ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cI
    cN
    wcel
    #
    w3a
    #
    cZ
    cV
    wcel
    #
    wa
    #
    cE
    cD
    cfv
    cI
    cI
    cE
    cI
    cZ
    cfv
    #
    cN
    cR
    cmarrep
    co
    co
    co
    #
    cD
    cfv
    #
    @6
    cI
    cI
    cE
    cN
    cR
    csubma
    co
    cfv
    co
    #
    cN
    cI
    csn
    #
    cdif
    #
    cR
    cmdat
    co
    #
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @6
    @5
    cE
    @7
    cD
    @5
    @7
    cE
    @5
    cR
    crg
    wcel
    #
    @0
    wa
    #
    @2
    @4
    wa
    #
    @7
    cE
    wceq
    @3
    @17
    @4
    @0
    @1
    @17
    @2
    @0
    @1
    wa
    #
    @0
    @16
    @1
    @16
    @0
    cR
    crngring
    #
    anim2i
    ancomd
    3adant3
    adantr
    #
    @3
    @2
    @4
    @0
    @1
    @2
    simp3
    #
    anim1i
    #
    cR
    cA
    cur
    cfv
    #
    cI
    cN
    cV
    cE
    cZ
    cramerimplem1.v
    cA
    cN
    cR
    cmat
    co
    #
    cur
    cramerimplem1.a
    fveq2i
    #
    cramerimplem1.e
    1marepvmarrepid
    syl2anc
    eqcomd
    fveq2d
    @5
    @8
    @7
    cN
    cR
    cmdat
    co
    #
    cfv
    #
    @15
    @5
    @7
    cD
    @27
    cD
    @27
    wceq
    @5
    cramerimplem1.d
    a1i
    fveq1d
    @5
    @1
    cE
    @25
    cbs
    cfv
    #
    wcel
    @2
    @6
    cR
    cbs
    cfv
    #
    wcel
    #
    @28
    @15
    wceq
    @0
    @1
    @2
    @4
    simpl2
    @5
    cE
    cI
    @24
    cZ
    cN
    cR
    cmatrepV
    co
    co
    cfv
    #
    @29
    cramerimplem1.e
    @5
    @17
    @4
    @2
    wa
    @32
    @29
    wcel
    @21
    @5
    @2
    @4
    @23
    ancomd
    cA
    @29
    cZ
    cR
    @24
    cI
    cN
    cV
    cramerimplem1.a
    @25
    cA
    cbs
    cA
    @25
    cramerimplem1.a
    eqcomi
    fveq2i
    cramerimplem1.v
    @24
    eqid
    ma1repvcl
    syl2anc
    syl5eqel
    @3
    @2
    @4
    @22
    adantr
    @3
    @4
    @31
    @2
    @0
    @4
    @31
    wi
    @1
    @4
    @2
    @31
    @2
    @31
    wi
    #
    cZ
    @30
    cN
    cmap
    co
    #
    cV
    cZ
    @34
    wcel
    cN
    @30
    cZ
    wf
    #
    @33
    cZ
    @30
    cN
    elmapi
    @35
    @2
    @31
    cN
    @30
    cI
    cZ
    ffvelrn
    ex
    syl
    cramerimplem1.v
    eleq2s
    com12
    3ad2ant3
    imp
    #
    cR
    @6
    cI
    cE
    cN
    smadiadetr
    syl22anc
    eqtrd
    @5
    @15
    @6
    @11
    cR
    cmat
    co
    #
    cur
    cfv
    #
    @12
    cfv
    #
    @14
    co
    @6
    cR
    cur
    cfv
    #
    @14
    co
    #
    @6
    @5
    @13
    @39
    @6
    @14
    @5
    @9
    @38
    @12
    @5
    @17
    @18
    @9
    @38
    wceq
    @21
    @23
    cR
    @24
    cI
    cN
    cV
    cE
    cZ
    cramerimplem1.v
    @26
    cramerimplem1.e
    1marepvsma1
    syl2anc
    fveq2d
    oveq2d
    @5
    @39
    @40
    @6
    @14
    @5
    @1
    @11
    cfn
    wcel
    #
    wa
    #
    @39
    @40
    wceq
    @3
    @43
    @4
    @0
    @1
    @43
    @2
    @19
    @42
    @1
    @0
    @42
    @1
    cN
    @10
    diffi
    anim1i
    ancomd
    3adant3
    adantr
    @37
    @12
    cR
    @40
    @38
    @11
    @12
    eqid
    @37
    eqid
    @38
    eqid
    @40
    eqid
    #
    mdet1
    syl
    oveq2d
    @5
    @16
    @31
    @41
    @6
    wceq
    @3
    @16
    @4
    @1
    @0
    @16
    @2
    @20
    3ad2ant2
    adantr
    @36
    @30
    cR
    @14
    @40
    @6
    @30
    eqid
    @14
    eqid
    @44
    ringridm
    syl2anc
    3eqtrd
    3eqtrd
end
