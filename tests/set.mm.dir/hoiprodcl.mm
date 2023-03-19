include "cc0.mm"
include "cpnf.mm"
include "cv.mm"
include "cico.mm"
include "ccom.mm"
include "cfv.mm"
include "cvol.mm"
include "cprod.mm"
include "cxr.mm"
include "wcel.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "wa.mm"
include "c1st.mm"
include "c2nd.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cif.mm"
include "cr.mm"
include "cxp.mm"
include "wf.mm"
include "adantr.mm"
include "simpr.mm"
include "fvovco.mm"
include "fveq2d.mm"
include "wceq.mm"
include "ffvelrnda.mm"
include "xp1st.mm"
include "syl.mm"
include "xp2nd.mm"
include "volico.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "resubcld.mm"
include "0red.mm"
include "ifcld.mm"
include "eqeltrd.mm"
include "fprodreclf.mm"
include "rexrd.mm"
include "cdm.mm"
include "cle.mm"
include "icombl.mm"
include "volge0.mm"
include "fprodge0.mm"
include "ltpnfd.mm"
include "elicod.mm"

theorem hoiprodcl
  let wph: wff ph
  let vk: setvar k
  let cI: class I
  let cX: class X
  let vx: setvar x
  assume hoiprodcl.1: |- F/ k ph
  assume hoiprodcl.2: |- ( ph -> X e. Fin )
  assume hoiprodcl.3: |- ( ph -> I : X --> ( RR X. RR ) )

  disjoint X k
  disjoint k x
  assert |- ( ph -> prod_ k e. X ( vol ` ( ( [,) o. I ) ` k ) ) e. ( 0 [,) +oo ) )

  proof
    wph
    cc0
    cpnf
    cX
    vk
    cv
    #
    cico
    cI
    ccom
    cfv
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cc0
    cxr
    wcel
    wph
    0xr
    a1i
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    wph
    @3
    wph
    cX
    @2
    vk
    hoiprodcl.1
    hoiprodcl.2
    wph
    @0
    cX
    wcel
    #
    wa
    #
    @2
    @0
    cI
    cfv
    #
    c1st
    cfv
    #
    @6
    c2nd
    cfv
    #
    clt
    wbr
    #
    @8
    @7
    cmin
    co
    #
    cc0
    cif
    #
    cr
    @5
    @2
    @7
    @8
    cico
    co
    #
    cvol
    cfv
    #
    @11
    @5
    @1
    @12
    cvol
    @5
    cI
    cico
    cr
    cr
    cX
    @0
    wph
    cX
    cr
    cr
    cxp
    #
    cI
    wf
    @4
    hoiprodcl.3
    adantr
    wph
    @4
    simpr
    fvovco
    #
    fveq2d
    @5
    @7
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @13
    @11
    wceq
    @5
    @6
    @14
    wcel
    #
    @16
    wph
    cX
    @14
    @0
    cI
    hoiprodcl.3
    ffvelrnda
    #
    @6
    cr
    cr
    xp1st
    syl
    #
    @5
    @18
    @17
    @19
    @6
    cr
    cr
    xp2nd
    syl
    #
    @7
    @8
    volico
    syl2anc
    eqtrd
    @5
    @9
    @10
    cc0
    cr
    @5
    @8
    @7
    @21
    @20
    resubcld
    @5
    0red
    ifcld
    eqeltrd
    #
    fprodreclf
    #
    rexrd
    wph
    cX
    @2
    vk
    hoiprodcl.1
    hoiprodcl.2
    @22
    @5
    @1
    cvol
    cdm
    #
    wcel
    cc0
    @2
    cle
    wbr
    @5
    @1
    @12
    @24
    @15
    @5
    @16
    @8
    cxr
    wcel
    @12
    @24
    wcel
    @20
    @5
    @8
    @21
    rexrd
    @7
    @8
    icombl
    syl2anc
    eqeltrd
    @1
    volge0
    syl
    fprodge0
    wph
    @3
    @23
    ltpnfd
    elicod
end
