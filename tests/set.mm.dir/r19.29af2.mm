include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "exp31.mm"
include "rexlimd.mm"
include "mpd.mm"

theorem r19.29af2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume r19.29af2.p: |- F/ x ph
  assume r19.29af2.c: |- F/ x ch
  assume r19.29af2.1: |- ( ( ( ph /\ x e. A ) /\ ps ) -> ch )
  assume r19.29af2.2: |- ( ph -> E. x e. A ps )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    vx
    cA
    wrex
    wch
    r19.29af2.2
    wph
    wps
    wch
    vx
    cA
    r19.29af2.p
    r19.29af2.c
    wph
    vx
    cv
    cA
    wcel
    wps
    wch
    r19.29af2.1
    exp31
    rexlimd
    mpd
end
