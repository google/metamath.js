include "wn.mm"
include "wa.mm"
include "wex.mm"
include "wo.mm"
include "wal.mm"
include "notnotb.mm"
include "anbi2i.mm"
include "exbii.mm"
include "ioran.mm"
include "exnal.mm"
include "3bitr2ri.mm"
include "notbii.mm"
include "exancom.mm"
include "3bitri.mm"
include "exmid.mm"
include "mpgbi.mm"
include "jca.mm"
include "bnj593.mm"
include "mto.mm"

theorem bnj1304
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bnj1304.1: |- ( ph -> E. x ps )
  assume bnj1304.2: |- ( ps -> ch )
  assume bnj1304.3: |- ( ps -> -. ch )


  assert |- -. ph

  proof
    wph
    wch
    wch
    wn
    #
    wa
    #
    vx
    wex
    #
    wch
    @0
    wo
    #
    @2
    wn
    #
    vx
    @3
    vx
    wal
    #
    @5
    wn
    #
    wn
    @0
    wch
    wa
    #
    vx
    wex
    #
    wn
    @4
    @5
    notnotb
    @6
    @8
    @8
    @0
    @0
    wn
    #
    wa
    #
    vx
    wex
    @3
    wn
    #
    vx
    wex
    @6
    @7
    @10
    vx
    wch
    @9
    @0
    wch
    notnotb
    anbi2i
    exbii
    @11
    @10
    vx
    wch
    @0
    ioran
    exbii
    @3
    vx
    exnal
    3bitr2ri
    notbii
    @8
    @2
    @0
    wch
    vx
    exancom
    notbii
    3bitri
    wch
    exmid
    mpgbi
    wph
    wps
    @1
    vx
    bnj1304.1
    wps
    wch
    @0
    bnj1304.2
    bnj1304.3
    jca
    bnj593
    mto
end
