include "cvv.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "copab.mm"
include "cmpt2.mm"
include "wceq.mm"
include "a1i.mm"
include "wb.mm"
include "oveq12.mm"
include "breqd.mm"
include "adantl.mm"
include "3expb.mm"
include "anbi12d.mm"
include "opabbidv.mm"
include "wcel.mm"
include "simpld.mm"
include "simprd.mm"
include "wi.mm"
include "wal.mm"
include "opabbrex.mm"
include "syl2anc.mm"
include "ovmpt2d.mm"

theorem sprmpt2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let cR: class R
  let ve: setvar e
  let cE: class E
  let cM: class M
  let cV: class V
  assume sprmpt2d.1: |- M = ( v e. _V , e e. _V |-> { <. x , y >. | ( x ( v R e ) y /\ ch ) } )
  assume sprmpt2d.2: |- ( ( ph /\ v = V /\ e = E ) -> ( ch <-> ps ) )
  assume sprmpt2d.3: |- ( ph -> ( V e. _V /\ E e. _V ) )
  assume sprmpt2d.4: |- ( ph -> A. x A. y ( x ( V R E ) y -> th ) )
  assume sprmpt2d.5: |- ( ph -> { <. x , y >. | th } e. _V )

  disjoint E e
  disjoint E v
  disjoint E x
  disjoint E y
  disjoint e v
  disjoint e x
  disjoint e y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint R e
  disjoint R v
  disjoint V e
  disjoint V v
  disjoint V x
  disjoint V y
  disjoint e ph
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint e ps
  disjoint ps v
  assert |- ( ph -> ( V M E ) = { <. x , y >. | ( x ( V R E ) y /\ ps ) } )

  proof
    wph
    vv
    ve
    cV
    cE
    cvv
    cvv
    vx
    cv
    #
    vy
    cv
    #
    vv
    cv
    #
    ve
    cv
    #
    cR
    co
    #
    wbr
    #
    wch
    wa
    #
    vx
    vy
    copab
    #
    @0
    @1
    cV
    cE
    cR
    co
    #
    wbr
    #
    wps
    wa
    #
    vx
    vy
    copab
    #
    cM
    cvv
    cM
    vv
    ve
    cvv
    cvv
    @7
    cmpt2
    wceq
    wph
    sprmpt2d.1
    a1i
    wph
    @2
    cV
    wceq
    #
    @3
    cE
    wceq
    #
    wa
    #
    wa
    #
    @6
    @10
    vx
    vy
    @15
    @5
    @9
    wch
    wps
    @14
    @5
    @9
    wb
    wph
    @14
    @4
    @8
    @0
    @1
    @2
    cV
    @3
    cE
    cR
    oveq12
    breqd
    adantl
    wph
    @12
    @13
    wch
    wps
    wb
    sprmpt2d.2
    3expb
    anbi12d
    opabbidv
    wph
    cV
    cvv
    wcel
    #
    cE
    cvv
    wcel
    #
    sprmpt2d.3
    simpld
    wph
    @16
    @17
    sprmpt2d.3
    simprd
    wph
    @9
    wth
    wi
    vy
    wal
    vx
    wal
    wth
    vx
    vy
    copab
    cvv
    wcel
    @11
    cvv
    wcel
    sprmpt2d.4
    sprmpt2d.5
    wth
    wps
    vx
    vy
    @8
    cvv
    opabbrex
    syl2anc
    ovmpt2d
end
