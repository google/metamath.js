include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "cn0.mm"
include "crab.mm"
include "wss.mm"
include "wral.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "albidv.mm"
include "elrab2.mm"
include "simplbi.mm"
include "eluznn0.mm"
include "ex.mm"
include "ssrdv.mm"
include "syl.mm"
include "simprbi.mm"
include "wa.mm"
include "eluzle.mm"
include "adantl.mm"
include "cxr.mm"
include "cr.mm"
include "nn0ssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "adantr.mm"
include "sseldi.mm"
include "sylan.mm"
include "cvv.mm"
include "vex.mm"
include "hashxrcl.mm"
include "mp1i.mm"
include "xrletr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "imim1d.mm"
include "ralrimdva.mm"
include "alimdv.mm"
include "mpd.mm"
include "ralcom4.mm"
include "sylibr.mm"
include "ssrab.mm"
include "sylanbrc.mm"
include "syl6sseqr.mm"

theorem ramtlecl
  let wph: wff ph
  let cT: class T
  let vn: setvar n
  let cM: class M
  let vs: setvar s
  assume ramtlecl.t: |- T = { n e. NN0 | A. s ( n <_ ( # ` s ) -> ph ) }

  disjoint n s
  disjoint M n
  disjoint M s
  disjoint n ph
  disjoint T n
  disjoint T s
  assert |- ( M e. T -> ( ZZ>= ` M ) C_ T )

  proof
    cM
    cT
    wcel
    #
    cM
    cuz
    cfv
    #
    vn
    cv
    #
    vs
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    wph
    wi
    #
    vs
    wal
    #
    vn
    cn0
    crab
    #
    cT
    @0
    @1
    cn0
    wss
    #
    @7
    vn
    @1
    wral
    #
    @1
    @8
    wss
    @0
    cM
    cn0
    wcel
    #
    @9
    @0
    @11
    cM
    @4
    cle
    wbr
    #
    wph
    wi
    #
    vs
    wal
    #
    @7
    @14
    vn
    cM
    cn0
    cT
    @2
    cM
    wceq
    #
    @6
    @13
    vs
    @15
    @5
    @12
    wph
    @2
    cM
    @4
    cle
    breq1
    imbi1d
    albidv
    ramtlecl.t
    elrab2
    #
    simplbi
    #
    @11
    vn
    @1
    cn0
    @11
    @2
    @1
    wcel
    #
    @2
    cn0
    wcel
    #
    @2
    cM
    eluznn0
    #
    ex
    ssrdv
    syl
    @0
    @6
    vn
    @1
    wral
    #
    vs
    wal
    #
    @10
    @0
    @14
    @22
    @0
    @11
    @14
    @16
    simprbi
    @0
    @13
    @21
    vs
    @0
    @13
    @6
    vn
    @1
    @0
    @18
    wa
    #
    @5
    @12
    wph
    @23
    cM
    @2
    cle
    wbr
    #
    @5
    @12
    @18
    @24
    @0
    cM
    @2
    eluzle
    adantl
    @23
    cM
    cxr
    wcel
    @2
    cxr
    wcel
    @4
    cxr
    wcel
    #
    @24
    @5
    wa
    @12
    wi
    @23
    cn0
    cxr
    cM
    cn0
    cr
    cxr
    nn0ssre
    ressxr
    sstri
    #
    @0
    @11
    @18
    @17
    adantr
    sseldi
    @23
    cn0
    cxr
    @2
    @26
    @0
    @11
    @18
    @19
    @17
    @20
    sylan
    sseldi
    @3
    cvv
    wcel
    @25
    @23
    vs
    vex
    @3
    cvv
    hashxrcl
    mp1i
    cM
    @2
    @4
    xrletr
    syl3anc
    mpand
    imim1d
    ralrimdva
    alimdv
    mpd
    @6
    vn
    vs
    @1
    ralcom4
    sylibr
    @7
    vn
    cn0
    @1
    ssrab
    sylanbrc
    ramtlecl.t
    syl6sseqr
end
