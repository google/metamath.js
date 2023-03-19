include "cuni.mm"
include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cfv.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "syl6ss.mm"
include "sspwuni.mm"
include "sylib.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "sylibr.mm"
include "cint.mm"
include "ssintub.mm"
include "wi.mm"
include "simpl.mm"
include "a1i.mm"
include "ss2rabi.mm"
include "intss.mm"
include "syl.mm"
include "syl5ss.mm"
include "c0.mm"
include "wne.mm"
include "intssuni.mm"
include "sstrd.mm"
include "wrex.mm"
include "eluni2.mm"
include "w3a.mm"
include "cun.mm"
include "clmod.mm"
include "simpll1.mm"
include "clvec.mm"
include "lveclmod.mm"
include "crpss.mm"
include "wor.mm"
include "simpll2.mm"
include "simplr.mm"
include "sorpssun.mm"
include "syl12anc.mm"
include "sseldd.mm"
include "sseldi.mm"
include "elpwid.mm"
include "ssdifssd.mm"
include "ssun2.mm"
include "ssdif.mm"
include "mp1i.mm"
include "lspss.mm"
include "syl3anc.mm"
include "simpr.mm"
include "wceq.mm"
include "sseq2.mm"
include "difeq1.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "notbid.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "simprbi.mm"
include "simprd.mm"
include "simpll3.mm"
include "elun1.mm"
include "rsp.mm"
include "sylc.mm"
include "pm2.65da.mm"
include "nrexdv.mm"
include "ciun.mm"
include "lbsextlem2.mm"
include "simpld.mm"
include "lssss.mm"
include "lspid.mm"
include "syl2anc.mm"
include "sseqtrd.mm"
include "3ad2ant1.mm"
include "syl6sseq.mm"
include "sseld.mm"
include "eliun.mm"
include "syl6ib.mm"
include "mtod.mm"
include "rexlimdv3a.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "jca.mm"
include "sylanbrc.mm"

theorem lbsextlem3
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vu: setvar u
  let cA: class A
  let cC: class C
  let cP: class P
  let cS: class S
  let cT: class T
  let cJ: class J
  let cN: class N
  let cV: class V
  let cW: class W
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vs: setvar s
  let vt: setvar t
  assume lbsext.v: |- V = ( Base ` W )
  assume lbsext.j: |- J = ( LBasis ` W )
  assume lbsext.n: |- N = ( LSpan ` W )
  assume lbsext.w: |- ( ph -> W e. LVec )
  assume lbsext.c: |- ( ph -> C C_ V )
  assume lbsext.x: |- ( ph -> A. x e. C -. x e. ( N ` ( C \ { x } ) ) )
  assume lbsext.s: |- S = { z e. ~P V | ( C C_ z /\ A. x e. z -. x e. ( N ` ( z \ { x } ) ) ) }
  assume lbsext.p: |- P = ( LSubSp ` W )
  assume lbsext.a: |- ( ph -> A C_ S )
  assume lbsext.z: |- ( ph -> A =/= (/) )
  assume lbsext.r: |- ( ph -> [C.] Or A )
  assume lbsext.t: |- T = U_ u e. A ( N ` ( u \ { x } ) )

  disjoint J x
  disjoint u x
  disjoint ph u
  disjoint ph x
  disjoint S u
  disjoint S x
  disjoint x z
  disjoint C x
  disjoint C z
  disjoint u z
  disjoint N u
  disjoint N x
  disjoint N z
  disjoint V u
  disjoint V x
  disjoint V z
  disjoint W u
  disjoint W x
  disjoint A u
  disjoint A x
  disjoint A z
  disjoint m n
  disjoint m r
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m ph
  disjoint n r
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n ph
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint ph r
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint ph w
  disjoint x y
  disjoint ph y
  disjoint s t
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint S s
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint S t
  disjoint S w
  disjoint S y
  disjoint T m
  disjoint T n
  disjoint T r
  disjoint T v
  disjoint T w
  disjoint m z
  disjoint N m
  disjoint n z
  disjoint N n
  disjoint w z
  disjoint N w
  disjoint y z
  disjoint N y
  disjoint V w
  disjoint W m
  disjoint W n
  disjoint W r
  disjoint W v
  disjoint W w
  disjoint m s
  disjoint m t
  disjoint A m
  disjoint n s
  disjoint n t
  disjoint A n
  disjoint s z
  disjoint A s
  disjoint t z
  disjoint A t
  disjoint A y
  assert |- ( ph -> U. A e. S )

  proof
    wph
    cA
    cuni
    #
    cV
    cpw
    #
    wcel
    #
    cC
    @0
    wss
    #
    vx
    cv
    #
    @0
    @4
    csn
    #
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    @0
    wral
    #
    wa
    #
    @0
    cS
    wcel
    wph
    @0
    cV
    wss
    #
    @2
    wph
    cA
    @1
    wss
    @12
    wph
    cA
    cS
    @1
    lbsext.a
    cS
    cC
    vz
    cv
    #
    wss
    #
    @4
    @13
    @5
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    @13
    wral
    #
    wa
    #
    vz
    @1
    crab
    #
    @1
    lbsext.s
    @20
    vz
    @1
    ssrab2
    eqsstri
    #
    syl6ss
    cA
    cV
    sspwuni
    sylib
    @0
    cV
    cV
    cW
    cbs
    cfv
    cvv
    lbsext.v
    cW
    cbs
    fvex
    eqeltri
    elpw2
    sylibr
    wph
    @3
    @10
    wph
    cC
    cA
    cint
    #
    @0
    wph
    cC
    @14
    vz
    @1
    crab
    #
    cint
    #
    @23
    vz
    cC
    @1
    ssintub
    wph
    cA
    @24
    wss
    @25
    @23
    wss
    wph
    cA
    cS
    @24
    lbsext.a
    cS
    @21
    @24
    lbsext.s
    @20
    @14
    vz
    @1
    @20
    @14
    wi
    @13
    @1
    wcel
    @14
    @19
    simpl
    a1i
    ss2rabi
    eqsstri
    syl6ss
    cA
    @24
    intss
    syl
    syl5ss
    wph
    cA
    c0
    wne
    @23
    @0
    wss
    lbsext.z
    cA
    intssuni
    syl
    sstrd
    wph
    @9
    vx
    @0
    @4
    @0
    wcel
    @4
    vy
    cv
    #
    wcel
    #
    vy
    cA
    wrex
    wph
    @9
    vy
    @4
    cA
    eluni2
    wph
    @27
    @9
    vy
    cA
    wph
    @26
    cA
    wcel
    #
    @27
    w3a
    #
    @8
    @4
    vu
    cv
    #
    @5
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    vu
    cA
    wrex
    #
    @29
    @33
    vu
    cA
    @29
    @30
    cA
    wcel
    #
    wa
    #
    @33
    @4
    @26
    @30
    cun
    #
    @5
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    @36
    @33
    wa
    #
    @32
    @39
    @4
    @41
    cW
    clmod
    wcel
    #
    @38
    cV
    wss
    @31
    @38
    wss
    #
    @32
    @39
    wss
    @41
    wph
    @42
    wph
    @28
    @27
    @35
    @33
    simpll1
    #
    wph
    cW
    clvec
    wcel
    @42
    lbsext.w
    cW
    lveclmod
    syl
    #
    syl
    @41
    @37
    cV
    @5
    @41
    @37
    cV
    @41
    cS
    @1
    @37
    @22
    @41
    cA
    cS
    @37
    @41
    wph
    cA
    cS
    wss
    @44
    lbsext.a
    syl
    @41
    cA
    crpss
    wor
    #
    @28
    @35
    @37
    cA
    wcel
    @41
    wph
    @46
    @44
    lbsext.r
    syl
    wph
    @28
    @27
    @35
    @33
    simpll2
    @29
    @35
    @33
    simplr
    cA
    @26
    @30
    sorpssun
    syl12anc
    sseldd
    #
    sseldi
    elpwid
    ssdifssd
    @30
    @37
    wss
    @43
    @41
    @30
    @26
    ssun2
    @30
    @37
    @5
    ssdif
    mp1i
    @31
    @38
    cN
    cV
    cW
    lbsext.v
    lbsext.n
    lspss
    syl3anc
    @36
    @33
    simpr
    sseldd
    @41
    @40
    wn
    #
    vx
    @37
    wral
    #
    @4
    @37
    wcel
    #
    @48
    @41
    @37
    cS
    wcel
    #
    @49
    @47
    @51
    cC
    @37
    wss
    #
    @49
    @51
    @37
    @1
    wcel
    @52
    @49
    wa
    #
    @20
    @53
    vz
    @37
    @1
    cS
    @13
    @37
    wceq
    #
    @14
    @52
    @19
    @49
    @13
    @37
    cC
    sseq2
    @18
    @48
    vx
    @13
    @37
    @54
    @17
    @40
    @54
    @16
    @39
    @4
    @54
    @15
    @38
    cN
    @13
    @37
    @5
    difeq1
    fveq2d
    eleq2d
    notbid
    raleqbi1dv
    anbi12d
    lbsext.s
    elrab2
    simprbi
    simprd
    syl
    @41
    @27
    @50
    wph
    @28
    @27
    @35
    @33
    simpll3
    @4
    @26
    @30
    elun1
    syl
    @48
    vx
    @37
    rsp
    sylc
    pm2.65da
    nrexdv
    @29
    @8
    @4
    vu
    cA
    @32
    ciun
    #
    wcel
    @34
    @29
    @7
    @55
    @4
    @29
    @7
    cT
    @55
    wph
    @28
    @7
    cT
    wss
    @27
    wph
    @7
    cT
    cN
    cfv
    #
    cT
    wph
    @42
    cT
    cV
    wss
    #
    @6
    cT
    wss
    #
    @7
    @56
    wss
    @45
    wph
    cT
    cP
    wcel
    #
    @57
    wph
    @59
    @58
    wph
    vx
    vz
    vu
    cA
    cC
    cP
    cS
    cT
    cJ
    cN
    cV
    cW
    lbsext.v
    lbsext.j
    lbsext.n
    lbsext.w
    lbsext.c
    lbsext.x
    lbsext.s
    lbsext.p
    lbsext.a
    lbsext.z
    lbsext.r
    lbsext.t
    lbsextlem2
    #
    simpld
    #
    cP
    cT
    cV
    cW
    lbsext.v
    lbsext.p
    lssss
    syl
    wph
    @59
    @58
    @60
    simprd
    @6
    cT
    cN
    cV
    cW
    lbsext.v
    lbsext.n
    lspss
    syl3anc
    wph
    @42
    @59
    @56
    cT
    wceq
    @45
    @61
    cP
    cT
    cN
    cW
    lbsext.p
    lbsext.n
    lspid
    syl2anc
    sseqtrd
    3ad2ant1
    lbsext.t
    syl6sseq
    sseld
    vu
    @4
    cA
    @32
    eliun
    syl6ib
    mtod
    rexlimdv3a
    syl5bi
    ralrimiv
    jca
    @20
    @11
    vz
    @0
    @1
    cS
    @13
    @0
    wceq
    #
    @14
    @3
    @19
    @10
    @13
    @0
    cC
    sseq2
    @18
    @9
    vx
    @13
    @0
    @62
    @17
    @8
    @62
    @16
    @7
    @4
    @62
    @15
    @6
    cN
    @13
    @0
    @5
    difeq1
    fveq2d
    eleq2d
    notbid
    raleqbi1dv
    anbi12d
    lbsext.s
    elrab2
    sylanbrc
end
