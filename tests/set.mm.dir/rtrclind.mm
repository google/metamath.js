include "crtcl.mm"
include "cfv.mm"
include "crtrcl.mm"
include "wceq.mm"
include "wbr.mm"
include "wi.mm"
include "dfrtrcl2.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "cn0.mm"
include "wrex.mm"
include "wa.mm"
include "dfrtrclrec2.mm"
include "biimpac.mm"
include "wcel.mm"
include "simprl.mm"
include "simprrr.mm"
include "simprrl.mm"
include "relexpind.mm"
include "syl3c.mm"
include "anassrs.mm"
include "expcom.mm"
include "rexlimiv.mm"
include "mpcom.mm"
include "breq.mm"
include "imbi1d.mm"
include "syl5ibr.mm"

theorem rtrclind
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
  let cX: class X
  let vn: setvar n
  assume rtrclind.1: |- ( et -> Rel R )
  assume rtrclind.2: |- ( et -> R e. _V )
  assume rtrclind.3: |- ( et -> S e. _V )
  assume rtrclind.4: |- ( et -> X e. _V )
  assume rtrclind.5: |- ( i = S -> ( ph <-> ch ) )
  assume rtrclind.6: |- ( i = x -> ( ph <-> ps ) )
  assume rtrclind.7: |- ( i = j -> ( ph <-> th ) )
  assume rtrclind.8: |- ( x = X -> ( ps <-> ta ) )
  assume rtrclind.9: |- ( et -> ch )
  assume rtrclind.10: |- ( et -> ( j R x -> ( th -> ps ) ) )

  disjoint R x
  disjoint R i
  disjoint R j
  disjoint i j
  disjoint i x
  disjoint j x
  disjoint S x
  disjoint S i
  disjoint S j
  disjoint X x
  disjoint et x
  disjoint et i
  disjoint et j
  disjoint ta x
  disjoint i ps
  disjoint j ps
  disjoint i th
  disjoint j ph
  disjoint ph x
  disjoint ch i
  disjoint R n
  disjoint n x
  disjoint S n
  disjoint X n
  disjoint et n
  disjoint n ta
  assert |- ( et -> ( S ( t* ` R ) X -> ta ) )

  proof
    cR
    crtcl
    cfv
    #
    cR
    crtrcl
    cfv
    #
    wceq
    #
    wet
    cS
    cX
    @0
    wbr
    #
    wta
    wi
    #
    wet
    cR
    rtrclind.1
    rtrclind.2
    dfrtrcl2
    wet
    @4
    @2
    cS
    cX
    @1
    wbr
    #
    wta
    wi
    @5
    wet
    wta
    cS
    cX
    cR
    vn
    cv
    #
    crelexp
    co
    wbr
    #
    vn
    cn0
    wrex
    #
    @5
    wet
    wa
    #
    wta
    wet
    @5
    @8
    wet
    cS
    cX
    cR
    vn
    rtrclind.1
    rtrclind.2
    dfrtrclrec2
    biimpac
    @7
    @9
    wta
    wi
    #
    vn
    cn0
    @7
    @6
    cn0
    wcel
    #
    @10
    @9
    @7
    @11
    wa
    #
    wta
    @5
    wet
    @12
    wta
    @5
    wet
    @12
    wa
    wa
    wet
    @11
    @7
    wta
    @5
    wet
    @12
    simprl
    @5
    wet
    @7
    @11
    simprrr
    @5
    wet
    @7
    @11
    simprrl
    wph
    wps
    wch
    wth
    wta
    wet
    vx
    cR
    cS
    vi
    vj
    vn
    cX
    rtrclind.1
    rtrclind.2
    rtrclind.3
    rtrclind.4
    rtrclind.5
    rtrclind.6
    rtrclind.7
    rtrclind.8
    rtrclind.9
    rtrclind.10
    relexpind
    syl3c
    anassrs
    expcom
    expcom
    rexlimiv
    mpcom
    expcom
    @2
    @3
    @5
    wta
    cS
    cX
    @0
    @1
    breq
    imbi1d
    syl5ibr
    mpcom
end
