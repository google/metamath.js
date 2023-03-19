include "wcel.mm"
include "wbr.mm"
include "cvv.mm"
include "relopabi.mm"
include "brrelexi.mm"
include "wi.mm"
include "wa.mm"
include "brabg.mm"
include "biimpd.mm"
include "ex.mm"
include "com3l.mm"
include "mpdi.mm"
include "exbiri.mm"
include "impbid.mm"

theorem brabg2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  assume brabg2.1: |- ( x = A -> ( ph <-> ps ) )
  assume brabg2.2: |- ( y = B -> ( ps <-> ch ) )
  assume brabg2.3: |- R = { <. x , y >. | ph }
  assume brabg2.4: |- ( ch -> A e. C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ch x
  disjoint ch y
  assert |- ( B e. D -> ( A R B <-> ch ) )

  proof
    cB
    cD
    wcel
    #
    cA
    cB
    cR
    wbr
    #
    wch
    @0
    @1
    cA
    cvv
    wcel
    #
    wch
    cA
    cB
    cR
    wph
    vx
    vy
    cR
    brabg2.3
    relopabi
    brrelexi
    @2
    @0
    @1
    wch
    @2
    @0
    @1
    wch
    wi
    @2
    @0
    wa
    @1
    wch
    wph
    wps
    wch
    vx
    vy
    cA
    cB
    cvv
    cD
    cR
    brabg2.1
    brabg2.2
    brabg2.3
    brabg
    biimpd
    ex
    com3l
    mpdi
    @0
    wch
    cA
    cC
    wcel
    #
    @1
    brabg2.4
    @3
    @0
    wch
    @1
    @3
    @0
    @1
    wch
    wph
    wps
    wch
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    brabg2.1
    brabg2.2
    brabg2.3
    brabg
    exbiri
    com3l
    mpdi
    impbid
end
