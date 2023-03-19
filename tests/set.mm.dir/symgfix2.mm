include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "csn.mm"
include "wrex.mm"
include "eldif.mm"
include "ianor.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "xchnxbir.mm"
include "anbi2i.mm"
include "bitri.mm"
include "wi.mm"
include "pm2.21.mm"
include "wral.mm"
include "symgmov2.mm"
include "eqeq2.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "wne.mm"
include "wb.mm"
include "eqcoms.mm"
include "notbid.mm"
include "fveq2.mm"
include "necon3bi.mm"
include "syl6bi.mm"
include "com12.mm"
include "pm4.71rd.mm"
include "rexdifsn.mm"
include "syl6bbr.mm"
include "syl5ibcom.mm"
include "ex.mm"
include "com13.mm"
include "syl5.mm"
include "jaoi.mm"
include "impd.mm"
include "syl5bi.mm"

theorem symgfix2
  let cP: class P
  let cQ: class Q
  let vk: setvar k
  let cK: class K
  let cL: class L
  let cN: class N
  let vq: setvar q
  let vl: setvar l
  assume symgfix2.p: |- P = ( Base ` ( SymGrp ` N ) )

  disjoint N k
  disjoint Q k
  disjoint K k
  disjoint K q
  disjoint k q
  disjoint L k
  disjoint L q
  disjoint P q
  disjoint Q q
  disjoint K l
  disjoint k l
  disjoint l q
  disjoint L l
  disjoint N l
  disjoint P l
  disjoint Q l
  assert |- ( L e. N -> ( Q e. ( P \ { q e. P | ( q ` K ) = L } ) -> E. k e. ( N \ { K } ) ( Q ` k ) = L ) )

  proof
    cQ
    cP
    cK
    vq
    cv
    #
    cfv
    #
    cL
    wceq
    #
    vq
    cP
    crab
    #
    cdif
    wcel
    #
    cQ
    cP
    wcel
    #
    @5
    wn
    #
    cK
    cQ
    cfv
    #
    cL
    wceq
    #
    wn
    #
    wo
    #
    wa
    #
    cL
    cN
    wcel
    #
    vk
    cv
    #
    cQ
    cfv
    #
    cL
    wceq
    #
    vk
    cN
    cK
    csn
    cdif
    wrex
    #
    @4
    @5
    cQ
    @3
    wcel
    #
    wn
    #
    wa
    @11
    cQ
    cP
    @3
    eldif
    @18
    @10
    @5
    @5
    @8
    wa
    @10
    @17
    @5
    @8
    ianor
    @2
    @8
    vq
    cQ
    cP
    @0
    cQ
    wceq
    @1
    @7
    cL
    cK
    @0
    cQ
    fveq1
    eqeq1d
    elrab
    xchnxbir
    anbi2i
    bitri
    @12
    @5
    @10
    @16
    @10
    @5
    @12
    @16
    @6
    @5
    @12
    @16
    wi
    #
    wi
    @9
    @5
    @19
    pm2.21
    @5
    @14
    vl
    cv
    #
    wceq
    #
    vk
    cN
    wrex
    #
    vl
    cN
    wral
    #
    @9
    @19
    cP
    cQ
    vk
    vl
    cN
    symgfix2.p
    symgmov2
    @12
    @23
    @9
    @16
    @12
    @23
    @9
    @16
    wi
    @12
    @23
    wa
    @15
    vk
    cN
    wrex
    #
    @9
    @16
    @22
    @24
    vl
    cL
    cN
    @20
    cL
    wceq
    @21
    @15
    vk
    cN
    @20
    cL
    @14
    eqeq2
    rexbidv
    rspcva
    @9
    @24
    @13
    cK
    wne
    #
    @15
    wa
    #
    vk
    cN
    wrex
    @16
    @9
    @15
    @26
    vk
    cN
    @9
    @15
    @25
    @15
    @9
    @25
    @15
    @9
    @7
    @14
    wceq
    #
    wn
    @25
    @15
    @8
    @27
    @8
    @27
    wb
    cL
    @14
    cL
    @14
    @7
    eqeq2
    eqcoms
    notbid
    @27
    @13
    cK
    @27
    cK
    @13
    cK
    @13
    cQ
    fveq2
    eqcoms
    necon3bi
    syl6bi
    com12
    pm4.71rd
    rexbidv
    @15
    vk
    cN
    cK
    rexdifsn
    syl6bbr
    syl5ibcom
    ex
    com13
    syl5
    jaoi
    com13
    impd
    syl5bi
end
