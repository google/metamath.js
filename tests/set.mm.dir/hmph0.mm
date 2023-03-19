include "c0.mm"
include "csn.mm"
include "chmph.mm"
include "wbr.mm"
include "wceq.mm"
include "c1o.mm"
include "cen.mm"
include "hmphen.mm"
include "df1o2.mm"
include "syl6breqr.mm"
include "ctop.mm"
include "wcel.mm"
include "wb.mm"
include "hmphtop1.mm"
include "en1top.mm"
include "syl.mm"
include "mpbid.mm"
include "id.mm"
include "sn0top.mm"
include "hmphref.mm"
include "ax-mp.mm"
include "syl6eqbr.mm"
include "impbii.mm"

theorem hmph0
  let cJ: class J


  assert |- ( J ~= { (/) } <-> J = { (/) } )

  proof
    cJ
    c0
    csn
    #
    chmph
    wbr
    #
    cJ
    @0
    wceq
    #
    @1
    cJ
    c1o
    cen
    wbr
    #
    @2
    @1
    cJ
    @0
    c1o
    cen
    cJ
    @0
    hmphen
    df1o2
    syl6breqr
    @1
    cJ
    ctop
    wcel
    @3
    @2
    wb
    cJ
    @0
    hmphtop1
    cJ
    en1top
    syl
    mpbid
    @2
    cJ
    @0
    @0
    chmph
    @2
    id
    @0
    ctop
    wcel
    @0
    @0
    chmph
    wbr
    sn0top
    @0
    hmphref
    ax-mp
    syl6eqbr
    impbii
end
