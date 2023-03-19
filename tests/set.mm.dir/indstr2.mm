include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wo.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "elnn1uz2.mm"
include "wb.mm"
include "wa.mm"
include "wn.mm"
include "nnnlt1.mm"
include "adantl.mm"
include "breq2.mm"
include "adantr.mm"
include "mtbird.mm"
include "pm2.21d.mm"
include "ralrimiva.mm"
include "pm5.5.mm"
include "syl.mm"
include "bitrd.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "sylbi.mm"
include "indstr.mm"

theorem indstr2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume indstr2.1: |- ( x = 1 -> ( ph <-> ch ) )
  assume indstr2.2: |- ( x = y -> ( ph <-> ps ) )
  assume indstr2.3: |- ch
  assume indstr2.4: |- ( x e. ( ZZ>= ` 2 ) -> ( A. y e. NN ( y < x -> ps ) -> ph ) )

  disjoint ph y
  disjoint ps x
  disjoint x y
  assert |- ( x e. NN -> ph )

  proof
    wph
    wps
    vx
    vy
    indstr2.2
    vx
    cv
    #
    cn
    wcel
    @0
    c1
    wceq
    #
    @0
    c2
    cuz
    cfv
    wcel
    #
    wo
    vy
    cv
    #
    @0
    clt
    wbr
    #
    wps
    wi
    #
    vy
    cn
    wral
    #
    wph
    wi
    #
    @0
    elnn1uz2
    @1
    @7
    @2
    @1
    @7
    wch
    indstr2.3
    @1
    @7
    wph
    wch
    @1
    @6
    @7
    wph
    wb
    @1
    @5
    vy
    cn
    @1
    @3
    cn
    wcel
    #
    wa
    #
    @4
    wps
    @9
    @4
    @3
    c1
    clt
    wbr
    #
    @8
    @10
    wn
    @1
    @3
    nnnlt1
    adantl
    @1
    @4
    @10
    wb
    @8
    @0
    c1
    @3
    clt
    breq2
    adantr
    mtbird
    pm2.21d
    ralrimiva
    @6
    wph
    pm5.5
    syl
    indstr2.1
    bitrd
    mpbiri
    indstr2.4
    jaoi
    sylbi
    indstr
end
