include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "cres.mm"
include "csumge0.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "nfv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "simpr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "adantr.mm"
include "elinel1.mm"
include "elpwi.mm"
include "syl.mm"
include "adantl.mm"
include "fssresd.mm"
include "sge0xrcl.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "rnmptss.mm"
include "crp.mm"
include "cxad.mm"
include "wbr.mm"
include "wrex.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfrex.mm"
include "w3a.mm"
include "cvv.mm"
include "id.mm"
include "fvexd.mm"
include "elrnmpt1.mm"
include "syl2anc.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "rspce.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "supxrge.mm"
include "sge0sup.mm"
include "eqcomd.mm"
include "breqtrd.mm"

theorem sge0gerp
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cF: class F
  let cV: class V
  let cX: class X
  let vy: setvar y
  let vk: setvar k
  assume sge0gerp.x: |- ( ph -> X e. V )
  assume sge0gerp.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )
  assume sge0gerp.a: |- ( ph -> A e. RR* )
  assume sge0gerp.z: |- ( ( ph /\ x e. RR+ ) -> E. z e. ( ~P X i^i Fin ) A <_ ( ( sum^ ` ( F |` z ) ) +e x ) )

  disjoint A x
  disjoint A z
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint X x
  disjoint X z
  disjoint ph x
  disjoint ph z
  disjoint A y
  disjoint x y
  disjoint y z
  disjoint F y
  disjoint X y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> A <_ ( sum^ ` F ) )

  proof
    wph
    cA
    vz
    cX
    cpw
    #
    cfn
    cin
    #
    cF
    vz
    cv
    #
    cres
    #
    csumge0
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cF
    csumge0
    cfv
    #
    cle
    wph
    vx
    vy
    @6
    cA
    wph
    vx
    nfv
    wph
    @4
    cxr
    wcel
    #
    vz
    @1
    wral
    @6
    cxr
    wss
    wph
    @9
    vz
    @1
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @3
    @1
    @2
    wph
    @10
    simpr
    @11
    cX
    cc0
    cpnf
    cicc
    co
    #
    @2
    cF
    wph
    cX
    @12
    cF
    wf
    @10
    sge0gerp.f
    adantr
    @10
    @2
    cX
    wss
    #
    wph
    @10
    @2
    @0
    wcel
    @13
    @2
    @0
    cfn
    elinel1
    @2
    cX
    elpwi
    syl
    adantl
    fssresd
    sge0xrcl
    ralrimiva
    vz
    @1
    @4
    cxr
    @5
    @5
    eqid
    #
    rnmptss
    syl
    sge0gerp.a
    wph
    vx
    cv
    #
    crp
    wcel
    wa
    #
    cA
    @4
    @15
    cxad
    co
    #
    cle
    wbr
    #
    vz
    @1
    wrex
    cA
    vy
    cv
    #
    @15
    cxad
    co
    #
    cle
    wbr
    #
    vy
    @6
    wrex
    #
    sge0gerp.z
    @16
    @18
    @22
    vz
    @1
    @16
    vz
    nfv
    @21
    vz
    vy
    @6
    vz
    @5
    vz
    @1
    @4
    nfmpt1
    nfrn
    @21
    vz
    nfv
    nfrex
    @16
    @10
    @18
    @22
    @16
    @10
    @18
    w3a
    @4
    @6
    wcel
    #
    @18
    @22
    @10
    @16
    @23
    @18
    @10
    @10
    @4
    cvv
    wcel
    @23
    @10
    id
    @10
    @3
    csumge0
    fvexd
    vz
    @1
    @4
    @5
    cvv
    @14
    elrnmpt1
    syl2anc
    3ad2ant2
    @16
    @10
    @18
    simp3
    @21
    @18
    vy
    @4
    @6
    @18
    vy
    nfv
    @19
    @4
    wceq
    @20
    @17
    cA
    cle
    @19
    @4
    @15
    cxad
    oveq1
    breq2d
    rspce
    syl2anc
    3exp
    rexlimd
    mpd
    supxrge
    wph
    @8
    @7
    wph
    vz
    cF
    cV
    cX
    sge0gerp.x
    sge0gerp.f
    sge0sup
    eqcomd
    breqtrd
end
