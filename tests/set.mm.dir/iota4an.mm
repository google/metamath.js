include "wa.mm"
include "weu.mm"
include "cio.mm"
include "wsbc.mm"
include "iota4.mm"
include "wi.mm"
include "cvv.mm"
include "wcel.mm"
include "iotaex.mm"
include "simpl.mm"
include "sbcth.mm"
include "ax-mp.mm"
include "wb.mm"
include "sbcimg.mm"
include "mpbi.mm"
include "syl.mm"

theorem iota4an
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E! x ( ph /\ ps ) -> [. ( iota x ( ph /\ ps ) ) / x ]. ph )

  proof
    wph
    wps
    wa
    #
    vx
    weu
    @0
    vx
    @0
    vx
    cio
    #
    wsbc
    #
    wph
    vx
    @1
    wsbc
    #
    @0
    vx
    iota4
    @0
    wph
    wi
    #
    vx
    @1
    wsbc
    #
    @2
    @3
    wi
    #
    @1
    cvv
    wcel
    #
    @5
    @0
    vx
    iotaex
    #
    @4
    vx
    @1
    cvv
    wph
    wps
    simpl
    sbcth
    ax-mp
    @7
    @5
    @6
    wb
    @8
    @0
    wph
    vx
    @1
    cvv
    sbcimg
    ax-mp
    mpbi
    syl
end
