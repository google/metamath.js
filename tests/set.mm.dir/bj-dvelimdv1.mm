include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wnf.mm"
include "wi.mm"
include "nfeqf2.mm"
include "nfimt.mm"
include "syl2imc.mm"
include "alrimdv.mm"
include "bj-nfalt.mm"
include "equsalvw.mm"
include "nfbii.mm"
include "bj-syl66ib.mm"

theorem bj-dvelimdv1
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
  assert |- ( ph -> ( -. A. x x = y -> F/ x ps ) )

  proof
    wph
    vx
    vy
    weq
    vx
    wal
    wn
    #
    wps
    vx
    wnf
    vz
    vy
    weq
    #
    wch
    wi
    #
    vx
    wnf
    #
    vz
    wal
    @2
    vz
    wal
    #
    vx
    wnf
    wph
    @0
    @3
    vz
    @0
    @1
    vx
    wnf
    wph
    wch
    vx
    wnf
    @3
    vx
    vy
    vz
    nfeqf2
    bj-dvelimdv.nf1
    @1
    wch
    vx
    nfimt
    syl2imc
    alrimdv
    @2
    vz
    vx
    bj-nfalt
    @4
    wps
    vx
    wch
    wps
    vz
    vy
    bj-dvelimdv.is
    equsalvw
    nfbii
    bj-syl66ib
end
