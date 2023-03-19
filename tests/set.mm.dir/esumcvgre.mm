include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cpnf.mm"
include "wceq.mm"
include "wn.mm"
include "cr.mm"
include "wrex.mm"
include "wral.mm"
include "cesum.mm"
include "nfre1.mm"
include "nfan.mm"
include "adantr.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "adantlr.mm"
include "simpr.mm"
include "esumpinfval.mm"
include "wne.mm"
include "wi.mm"
include "clt.mm"
include "wbr.mm"
include "ltpnf.mm"
include "syl.mm"
include "gtned.mm"
include "necom.mm"
include "imbi2i.mm"
include "mpbi.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "ralnex.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "wo.mm"
include "cxr.mm"
include "cmnf.mm"
include "iccssxr.mm"
include "sseli.mm"
include "xrge0neqmnf.mm"
include "xrnemnf.mm"
include "biimpi.mm"
include "syl2anc.mm"
include "orcomd.mm"
include "orcanai.mm"
include "mpdan.mm"

theorem esumcvgre
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cV: class V
  assume esumcvgre.0: |- F/ k ph
  assume esumcvgre.1: |- ( ph -> A e. V )
  assume esumcvgre.2: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume esumcvgre.3: |- ( ph -> sum* k e. A B e. RR )

  disjoint A k
  disjoint V k
  assert |- ( ( ph /\ k e. A ) -> B e. RR )

  proof
    wph
    vk
    cv
    cA
    wcel
    #
    wa
    #
    cB
    cpnf
    wceq
    #
    wn
    #
    cB
    cr
    wcel
    #
    wph
    @3
    vk
    cA
    wph
    @2
    vk
    cA
    wrex
    #
    wn
    @3
    vk
    cA
    wral
    wph
    @5
    cA
    cB
    vk
    cesum
    #
    cpnf
    wceq
    wph
    @5
    wa
    #
    cA
    cB
    vk
    cV
    wph
    @5
    vk
    esumcvgre.0
    @2
    vk
    cA
    nfre1
    nfan
    wph
    cA
    cV
    wcel
    @5
    esumcvgre.1
    adantr
    wph
    @0
    cB
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @5
    esumcvgre.2
    adantlr
    wph
    @5
    simpr
    esumpinfval
    @7
    @6
    cpnf
    @7
    cpnf
    @6
    wne
    #
    wi
    @7
    @6
    cpnf
    wne
    #
    wi
    wph
    @10
    @5
    wph
    @6
    cpnf
    esumcvgre.3
    wph
    @6
    cr
    wcel
    @6
    cpnf
    clt
    wbr
    esumcvgre.3
    @6
    ltpnf
    syl
    gtned
    adantr
    @10
    @11
    @7
    cpnf
    @6
    necom
    imbi2i
    mpbi
    neneqd
    pm2.65da
    @2
    vk
    cA
    ralnex
    sylibr
    r19.21bi
    @1
    @2
    @4
    @1
    @4
    @2
    @1
    @9
    @4
    @2
    wo
    #
    esumcvgre.2
    @9
    cB
    cxr
    wcel
    #
    cB
    cmnf
    wne
    #
    @12
    @8
    cxr
    cB
    cc0
    cpnf
    iccssxr
    sseli
    cB
    xrge0neqmnf
    @13
    @14
    wa
    @12
    cB
    xrnemnf
    biimpi
    syl2anc
    syl
    orcomd
    orcanai
    mpdan
end
