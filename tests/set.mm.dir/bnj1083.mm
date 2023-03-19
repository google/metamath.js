include "cv.mm"
include "wfn.mm"
include "w3a.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "df-rex.mm"
include "abeq2i.mm"
include "w-bnj17.mm"
include "bnj252.mm"
include "bitri.mm"
include "exbii.mm"
include "3bitr4i.mm"

theorem bnj1083
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cD: class D
  let vf: setvar f
  let vn: setvar n
  let cK: class K
  assume bnj1083.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1083.8: |- K = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }


  assert |- ( f e. K <-> E. n ch )

  proof
    vf
    cv
    #
    vn
    cv
    #
    wfn
    #
    wph
    wps
    w3a
    #
    vn
    cD
    wrex
    #
    @1
    cD
    wcel
    #
    @3
    wa
    #
    vn
    wex
    @0
    cK
    wcel
    wch
    vn
    wex
    @3
    vn
    cD
    df-rex
    @4
    vf
    cK
    bnj1083.8
    abeq2i
    wch
    @6
    vn
    wch
    @5
    @2
    wph
    wps
    w-bnj17
    @6
    bnj1083.3
    @5
    @2
    wph
    wps
    bnj252
    bitri
    exbii
    3bitr4i
end
