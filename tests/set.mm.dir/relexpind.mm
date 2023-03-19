include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cn0.mm"
include "crelexp.mm"
include "co.mm"
include "wbr.mm"
include "wi.mm"
include "wb.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi1d.mm"
include "imbi2d.mm"
include "imbi2.mm"
include "bibi1d.mm"
include "syl5ibr.mm"
include "mpcom.mm"
include "relexpindlem.mm"
include "vtoclg.mm"

theorem relexpind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vx: setvar x
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cX: class X
  assume relexpind.1: |- ( et -> Rel R )
  assume relexpind.2: |- ( et -> R e. _V )
  assume relexpind.3: |- ( et -> S e. _V )
  assume relexpind.4: |- ( et -> X e. _V )
  assume relexpind.5: |- ( i = S -> ( ph <-> ch ) )
  assume relexpind.6: |- ( i = x -> ( ph <-> ps ) )
  assume relexpind.7: |- ( i = j -> ( ph <-> th ) )
  assume relexpind.8: |- ( x = X -> ( ps <-> ta ) )
  assume relexpind.9: |- ( et -> ch )
  assume relexpind.10: |- ( et -> ( j R x -> ( th -> ps ) ) )

  disjoint i j
  disjoint i x
  disjoint R i
  disjoint j x
  disjoint R j
  disjoint R x
  disjoint S i
  disjoint S j
  disjoint S x
  disjoint X x
  disjoint n x
  disjoint j ph
  disjoint ph x
  disjoint i ps
  disjoint j ps
  disjoint ch i
  disjoint i th
  disjoint ta x
  disjoint et i
  disjoint et j
  disjoint et x
  assert |- ( et -> ( n e. NN0 -> ( S ( R ^r n ) X -> ta ) ) )

  proof
    cX
    cvv
    wcel
    wet
    vn
    cv
    #
    cn0
    wcel
    #
    cS
    cX
    cR
    @0
    crelexp
    co
    #
    wbr
    #
    wta
    wi
    #
    wi
    #
    relexpind.4
    wet
    @1
    cS
    vx
    cv
    #
    @2
    wbr
    #
    wps
    wi
    #
    wi
    #
    wi
    #
    wet
    @5
    wi
    #
    vx
    cX
    cvv
    wps
    wta
    wb
    #
    @6
    cX
    wceq
    #
    @10
    @11
    wb
    #
    relexpind.8
    @13
    @14
    @12
    wet
    @1
    @7
    wta
    wi
    #
    wi
    #
    wi
    #
    @11
    wb
    @13
    @16
    @5
    wet
    @13
    @15
    @4
    @1
    @13
    @7
    @3
    wta
    @6
    cX
    cS
    @2
    breq2
    imbi1d
    imbi2d
    imbi2d
    @12
    @10
    @17
    @11
    @12
    @9
    @16
    wet
    @12
    @8
    @15
    @1
    wps
    wta
    @7
    imbi2
    imbi2d
    imbi2d
    bibi1d
    syl5ibr
    mpcom
    wph
    wps
    wch
    wth
    wet
    vx
    cR
    cS
    vi
    vj
    vn
    relexpind.1
    relexpind.2
    relexpind.3
    relexpind.5
    relexpind.6
    relexpind.7
    relexpind.9
    relexpind.10
    relexpindlem
    vtoclg
    mpcom
end
