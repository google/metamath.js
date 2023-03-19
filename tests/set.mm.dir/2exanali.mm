include "wi.mm"
include "wn.mm"
include "wex.mm"
include "wal.mm"
include "wa.mm"
include "2nalexn.mm"
include "con1bii.mm"
include "annim.mm"
include "2exbii.mm"
include "xchnxbir.mm"

theorem 2exanali
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( -. E. x E. y ( ph /\ -. ps ) <-> A. x A. y ( ph -> ps ) )

  proof
    wph
    wps
    wi
    #
    wn
    #
    vy
    wex
    vx
    wex
    #
    @0
    vy
    wal
    vx
    wal
    #
    wph
    wps
    wn
    wa
    #
    vy
    wex
    vx
    wex
    @3
    @2
    @0
    vx
    vy
    2nalexn
    con1bii
    @4
    @1
    vx
    vy
    wph
    wps
    annim
    2exbii
    xchnxbir
end
