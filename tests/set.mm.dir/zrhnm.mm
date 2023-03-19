include "cnlm.mm"
include "wcel.mm"
include "cnrg.mm"
include "cnzr.mm"
include "w3a.mm"
include "cz.mm"
include "wa.mm"
include "cfv.mm"
include "cabs.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "cur.mm"
include "cmg.mm"
include "crg.mm"
include "wceq.mm"
include "simpl3.mm"
include "nzrring.mm"
include "syl.mm"
include "simpr.mm"
include "eqid.mm"
include "zrhmulg.mm"
include "fveq2d.mm"
include "syl2anc.mm"
include "simpl1.mm"
include "ringidcl.mm"
include "nmmulg.mm"
include "syl3anc.mm"
include "cnm.mm"
include "zlmnm.mm"
include "fveq1d.mm"
include "simpl2.mm"
include "c0g.mm"
include "wne.mm"
include "nrgring.mm"
include "nzrnz.mm"
include "zlm1.mm"
include "zlm0.mm"
include "isnzr.mm"
include "sylanbrc.mm"
include "nm1.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "cc.mm"
include "zcnd.mm"
include "abscl.mm"
include "recnd.mm"
include "mulid1.mm"
include "3syl.mm"

theorem zrhnm
  let cB: class B
  let cR: class R
  let cL: class L
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume nmmulg.x: |- B = ( Base ` R )
  assume nmmulg.n: |- N = ( norm ` R )
  assume nmmulg.z: |- Z = ( ZMod ` R )
  assume zrhnm.1: |- L = ( ZRHom ` R )


  assert |- ( ( ( Z e. NrmMod /\ Z e. NrmRing /\ R e. NzRing ) /\ M e. ZZ ) -> ( N ` ( L ` M ) ) = ( abs ` M ) )

  proof
    cZ
    cnlm
    wcel
    #
    cZ
    cnrg
    wcel
    #
    cR
    cnzr
    wcel
    #
    w3a
    #
    cM
    cz
    wcel
    #
    wa
    #
    cM
    cL
    cfv
    #
    cN
    cfv
    #
    cM
    cabs
    cfv
    #
    c1
    cmul
    co
    #
    @8
    @5
    @7
    cM
    cR
    cur
    cfv
    #
    cR
    cmg
    cfv
    #
    co
    #
    cN
    cfv
    #
    @8
    @10
    cN
    cfv
    #
    cmul
    co
    #
    @9
    @5
    cR
    crg
    wcel
    #
    @4
    @7
    @13
    wceq
    @5
    @2
    @16
    @0
    @1
    @2
    @4
    simpl3
    #
    cR
    nzrring
    syl
    #
    @3
    @4
    simpr
    #
    @16
    @4
    wa
    @6
    @12
    cN
    cR
    @11
    @10
    cL
    cM
    zrhnm.1
    @11
    eqid
    #
    @10
    eqid
    #
    zrhmulg
    fveq2d
    syl2anc
    @5
    @0
    @4
    @10
    cB
    wcel
    #
    @13
    @15
    wceq
    @0
    @1
    @2
    @4
    simpl1
    @19
    @5
    @16
    @22
    @18
    cB
    cR
    @10
    nmmulg.x
    @21
    ringidcl
    syl
    cB
    cR
    @11
    cM
    cN
    @10
    cZ
    nmmulg.x
    nmmulg.n
    nmmulg.z
    @20
    nmmulg
    syl3anc
    @5
    @14
    c1
    @8
    cmul
    @5
    @14
    @10
    cZ
    cnm
    cfv
    #
    cfv
    #
    c1
    @5
    @10
    cN
    @23
    @5
    @2
    cN
    @23
    wceq
    @17
    cR
    cN
    cnzr
    cZ
    nmmulg.z
    nmmulg.n
    zlmnm
    syl
    fveq1d
    @5
    @1
    cZ
    cnzr
    wcel
    #
    @24
    c1
    wceq
    @0
    @1
    @2
    @4
    simpl2
    #
    @5
    cZ
    crg
    wcel
    #
    @10
    cR
    c0g
    cfv
    #
    wne
    #
    @25
    @5
    @1
    @27
    @26
    cZ
    nrgring
    syl
    @5
    @2
    @29
    @17
    cR
    @10
    @28
    @21
    @28
    eqid
    #
    nzrnz
    syl
    cZ
    @10
    @28
    @10
    cR
    cZ
    nmmulg.z
    @21
    zlm1
    #
    cR
    cZ
    @28
    nmmulg.z
    @30
    zlm0
    isnzr
    sylanbrc
    cZ
    @10
    @23
    @23
    eqid
    @31
    nm1
    syl2anc
    eqtrd
    oveq2d
    3eqtrd
    @5
    cM
    cc
    wcel
    #
    @8
    cc
    wcel
    @9
    @8
    wceq
    @5
    cM
    @19
    zcnd
    @32
    @8
    cM
    abscl
    recnd
    @8
    mulid1
    3syl
    eqtrd
end
