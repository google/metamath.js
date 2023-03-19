include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "equsalvw.mm"
include "bicomi.mm"
include "nfv.mm"
include "nfan.mm"
include "wnf.mm"
include "nfeqf2.mm"
include "adantl.mm"
include "adantr.mm"
include "nfimd.mm"
include "nfald.mm"
include "nfxfrd.mm"

theorem bj-dvelimdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume bj-dvelimdv.nf: |- F/ x ph
  assume bj-dvelimdv.nf1: |- ( ph -> F/ x ch )
  assume bj-dvelimdv.is: |- ( z = y -> ( ch <-> ps ) )

  disjoint x z
  disjoint y z
  disjoint ph z
  disjoint ps z
  assert |- ( ( ph /\ -. A. x x = y ) -> F/ x ps )

  proof
    wps
    vz
    vy
    weq
    #
    wch
    wi
    #
    vz
    wal
    #
    wph
    vx
    vy
    weq
    vx
    wal
    wn
    #
    wa
    #
    vx
    @2
    wps
    wch
    wps
    vz
    vy
    bj-dvelimdv.is
    equsalvw
    bicomi
    @4
    @1
    vx
    vz
    wph
    @3
    vz
    wph
    vz
    nfv
    @3
    vz
    nfv
    nfan
    @4
    @0
    wch
    vx
    @3
    @0
    vx
    wnf
    wph
    vx
    vy
    vz
    nfeqf2
    adantl
    wph
    wch
    vx
    wnf
    @3
    bj-dvelimdv.nf1
    adantr
    nfimd
    nfald
    nfxfrd
end
