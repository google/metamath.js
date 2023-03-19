include "cio.mm"
include "weu.mm"
include "cab.mm"
include "cuni.mm"
include "c0.mm"
include "cif.mm"
include "wceq.mm"
include "wi.mm"
include "wn.mm"
include "iotauni.mm"
include "iotanul.mm"
include "ifval.mm"
include "mpbir2an.mm"

theorem dfiota4
  let wph: wff ph
  let vx: setvar x


  assert |- ( iota x ph ) = if ( E! x ph , U. { x | ph } , (/) )

  proof
    wph
    vx
    cio
    #
    wph
    vx
    weu
    #
    wph
    vx
    cab
    cuni
    #
    c0
    cif
    wceq
    @1
    @0
    @2
    wceq
    wi
    @1
    wn
    @0
    c0
    wceq
    wi
    wph
    vx
    iotauni
    wph
    vx
    iotanul
    @1
    @0
    @2
    c0
    ifval
    mpbir2an
end
