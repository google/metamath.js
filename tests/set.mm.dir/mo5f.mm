include "wmo.mm"
include "wsb.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "mo3.mm"
include "nfsb.mm"
include "nfan.mm"
include "nfv.mm"
include "nfim.mm"
include "nfal.mm"
include "sb8.mm"
include "sbim.mm"
include "sban.mm"
include "nfs1v.mm"
include "sbf.mm"
include "bicomi.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "equsb3.mm"
include "imbi12i.mm"
include "bitri.mm"
include "sbalv.mm"
include "albii.mm"
include "3bitri.mm"

theorem mo5f
  let wph: wff ph
  let vx: setvar x
  let vi: setvar i
  let vj: setvar j
  assume mo5f.1: |- F/ i ph
  assume mo5f.2: |- F/ j ph

  disjoint i j
  disjoint i x
  disjoint j x
  assert |- ( E* x ph <-> A. i A. j ( ( [ i / x ] ph /\ [ j / x ] ph ) -> i = j ) )

  proof
    wph
    vx
    wmo
    wph
    wph
    vx
    vj
    wsb
    #
    wa
    #
    vx
    vj
    weq
    #
    wi
    #
    vj
    wal
    #
    vx
    wal
    @4
    vx
    vi
    wsb
    #
    vi
    wal
    wph
    vx
    vi
    wsb
    #
    @0
    wa
    #
    vi
    vj
    weq
    #
    wi
    #
    vj
    wal
    #
    vi
    wal
    wph
    vx
    vj
    mo5f.2
    mo3
    @4
    vx
    vi
    @3
    vi
    vj
    @1
    @2
    vi
    wph
    @0
    vi
    mo5f.1
    wph
    vx
    vj
    vi
    mo5f.1
    nfsb
    nfan
    @2
    vi
    nfv
    nfim
    nfal
    sb8
    @5
    @10
    vi
    @3
    @9
    vx
    vi
    vj
    @3
    vx
    vi
    wsb
    @1
    vx
    vi
    wsb
    #
    @2
    vx
    vi
    wsb
    #
    wi
    @9
    @1
    @2
    vx
    vi
    sbim
    @11
    @7
    @12
    @8
    @11
    @6
    @0
    vx
    vi
    wsb
    #
    wa
    @7
    wph
    @0
    vx
    vi
    sban
    @0
    @13
    @6
    @13
    @0
    @0
    vx
    vi
    wph
    vx
    vj
    nfs1v
    sbf
    bicomi
    anbi2i
    bitr4i
    vi
    vx
    vj
    equsb3
    imbi12i
    bitri
    sbalv
    albii
    3bitri
end
