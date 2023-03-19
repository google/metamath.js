include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "clsp.mm"
include "wcel.mm"
include "wa.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "wss.mm"
include "wf.mm"
include "wb.mm"
include "adantr.mm"
include "simpr.mm"
include "eqid.mm"
include "limsupgle.mm"
include "syl211anc.mm"
include "cvv.mm"
include "reex.mm"
include "ssex.mm"
include "syl.mm"
include "xrex.mm"
include "a1i.mm"
include "fex2.mm"
include "syl3anc.mm"
include "limsupcl.mm"
include "xrleid.mm"
include "limsuple.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "limsupgf.mm"
include "ffvelrnda.mm"
include "xrletr.mm"
include "mpand.mm"
include "sylbird.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem limsupbnd1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vm: setvar m
  let vn: setvar n
  assume limsupbnd.1: |- ( ph -> B C_ RR )
  assume limsupbnd.2: |- ( ph -> F : B --> RR* )
  assume limsupbnd.3: |- ( ph -> A e. RR* )
  assume limsupbnd1.4: |- ( ph -> E. k e. RR A. j e. B ( k <_ j -> ( F ` j ) <_ A ) )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint B j
  disjoint B k
  disjoint F j
  disjoint F k
  disjoint j ph
  disjoint k ph
  disjoint j m
  disjoint k m
  disjoint A m
  disjoint j n
  disjoint k n
  disjoint m n
  disjoint B m
  disjoint B n
  disjoint F m
  disjoint F n
  disjoint m ph
  assert |- ( ph -> ( limsup ` F ) <_ A )

  proof
    wph
    vk
    cv
    #
    vj
    cv
    #
    cle
    wbr
    @1
    cF
    cfv
    cA
    cle
    wbr
    wi
    vj
    cB
    wral
    #
    vk
    cr
    wrex
    cF
    clsp
    cfv
    #
    cA
    cle
    wbr
    #
    limsupbnd1.4
    wph
    @2
    @4
    vk
    cr
    wph
    @0
    cr
    wcel
    #
    wa
    #
    @2
    @0
    vn
    cr
    cF
    vn
    cv
    cpnf
    cico
    co
    cima
    cxr
    cin
    cxr
    clt
    csup
    cmpt
    #
    cfv
    #
    cA
    cle
    wbr
    #
    @4
    @6
    cB
    cr
    wss
    #
    cB
    cxr
    cF
    wf
    #
    @5
    cA
    cxr
    wcel
    #
    @9
    @2
    wb
    wph
    @10
    @5
    limsupbnd.1
    adantr
    wph
    @11
    @5
    limsupbnd.2
    adantr
    wph
    @5
    simpr
    wph
    @12
    @5
    limsupbnd.3
    adantr
    #
    cA
    cB
    @0
    vj
    vn
    cF
    @7
    @7
    eqid
    #
    limsupgle
    syl211anc
    @6
    @3
    @8
    cle
    wbr
    #
    @9
    @4
    wph
    @15
    vk
    cr
    wph
    @3
    @3
    cle
    wbr
    #
    @15
    vk
    cr
    wral
    #
    wph
    @3
    cxr
    wcel
    #
    @16
    wph
    cF
    cvv
    wcel
    #
    @18
    wph
    @11
    cB
    cvv
    wcel
    #
    cxr
    cvv
    wcel
    #
    @19
    limsupbnd.2
    wph
    @10
    @20
    limsupbnd.1
    cB
    cr
    reex
    ssex
    syl
    @21
    wph
    xrex
    a1i
    cB
    cxr
    cF
    cvv
    cvv
    fex2
    syl3anc
    cF
    cvv
    limsupcl
    syl
    #
    @3
    xrleid
    syl
    wph
    @10
    @11
    @18
    @16
    @17
    wb
    limsupbnd.1
    limsupbnd.2
    @22
    @3
    cB
    vk
    vn
    cF
    @7
    @14
    limsuple
    syl3anc
    mpbid
    r19.21bi
    @6
    @18
    @8
    cxr
    wcel
    @12
    @15
    @9
    wa
    @4
    wi
    wph
    @18
    @5
    @22
    adantr
    wph
    cr
    cxr
    @0
    @7
    cr
    cxr
    @7
    wf
    wph
    vn
    cF
    @7
    @14
    limsupgf
    a1i
    ffvelrnda
    @13
    @3
    @8
    cA
    xrletr
    syl3anc
    mpand
    sylbird
    rexlimdva
    mpd
end
