include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wex.mm"
include "wa.mm"
include "wrex.mm"
include "wne.mm"
include "wb.mm"
include "eldifsn.mm"
include "hashle2pr.mm"
include "sylbi.mm"
include "eldifi.mm"
include "eleq1.mm"
include "cvv.mm"
include "wi.mm"
include "vex.mm"
include "prelpw.mm"
include "biimprd.mm"
include "mp2an.mm"
include "syl6bi.mm"
include "syl5com.mm"
include "pm4.71rd.mm"
include "2exbidv.mm"
include "r2ex.mm"
include "bicomi.mm"
include "a1i.mm"
include "3bitrd.mm"

theorem hashle2prv
  let cP: class P
  let cV: class V
  let va: setvar a
  let vb: setvar b

  disjoint P a
  disjoint P b
  disjoint a b
  disjoint V a
  disjoint V b
  assert |- ( P e. ( ~P V \ { (/) } ) -> ( ( # ` P ) <_ 2 <-> E. a e. V E. b e. V P = { a , b } ) )

  proof
    cP
    cV
    cpw
    #
    c0
    csn
    #
    cdif
    wcel
    #
    cP
    chash
    cfv
    c2
    cle
    wbr
    #
    cP
    va
    cv
    #
    vb
    cv
    #
    cpr
    #
    wceq
    #
    vb
    wex
    va
    wex
    #
    @4
    cV
    wcel
    @5
    cV
    wcel
    wa
    #
    @7
    wa
    #
    vb
    wex
    va
    wex
    #
    @7
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    @2
    cP
    @0
    wcel
    #
    cP
    c0
    wne
    wa
    @3
    @8
    wb
    cP
    @0
    c0
    eldifsn
    cP
    @0
    va
    vb
    hashle2pr
    sylbi
    @2
    @7
    @10
    va
    vb
    @2
    @7
    @9
    @2
    @13
    @7
    @9
    cP
    @0
    @1
    eldifi
    @7
    @13
    @6
    @0
    wcel
    #
    @9
    cP
    @6
    @0
    eleq1
    @4
    cvv
    wcel
    #
    @5
    cvv
    wcel
    #
    @14
    @9
    wi
    va
    vex
    vb
    vex
    @15
    @16
    wa
    @9
    @14
    @4
    @5
    cV
    cvv
    cvv
    prelpw
    biimprd
    mp2an
    syl6bi
    syl5com
    pm4.71rd
    2exbidv
    @11
    @12
    wb
    @2
    @12
    @11
    @7
    va
    vb
    cV
    cV
    r2ex
    bicomi
    a1i
    3bitrd
end
