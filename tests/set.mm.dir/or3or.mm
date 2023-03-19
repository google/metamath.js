include "wa.mm"
include "wxo.mm"
include "wo.mm"
include "wn.mm"
include "w3o.mm"
include "excxor.mm"
include "orbi2i.mm"
include "wb.mm"
include "orc.mm"
include "exmid.mm"
include "pm3.2.mm"
include "wi.mm"
include "biimp.mm"
include "iman.mm"
include "sylib.mm"
include "con2i.mm"
include "ex.mm"
include "df-xor.mm"
include "bicomi.mm"
include "syl6ib.mm"
include "orim12d.mm"
include "mpi.mm"
include "2thd.mm"
include "bicom.mm"
include "bibif.mm"
include "syl5bb.mm"
include "con2bid.mm"
include "syl6bb.mm"
include "biorf.mm"
include "simpl.mm"
include "con3i.mm"
include "syl.mm"
include "3bitr3d.mm"
include "pm2.61i.mm"
include "3orass.mm"
include "3bitr4i.mm"

theorem or3or
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/ ps ) <-> ( ( ph /\ ps ) \/ ( ph /\ -. ps ) \/ ( -. ph /\ ps ) ) )

  proof
    wph
    wps
    wa
    #
    wph
    wps
    wxo
    #
    wo
    #
    @0
    wph
    wps
    wn
    #
    wa
    #
    wph
    wn
    #
    wps
    wa
    #
    wo
    #
    wo
    wph
    wps
    wo
    #
    @0
    @4
    @6
    w3o
    @1
    @7
    @0
    wph
    wps
    excxor
    orbi2i
    wph
    @8
    @2
    wb
    wph
    @8
    @2
    wph
    wps
    orc
    wph
    wps
    @3
    wo
    @2
    wps
    exmid
    wph
    wps
    @0
    @3
    @1
    wph
    wps
    pm3.2
    wph
    @3
    wph
    wps
    wb
    #
    wn
    #
    @1
    wph
    @3
    @10
    @9
    @4
    @9
    wph
    wps
    wi
    @4
    wn
    wph
    wps
    biimp
    wph
    wps
    iman
    sylib
    con2i
    ex
    @1
    @10
    wph
    wps
    df-xor
    bicomi
    #
    syl6ib
    orim12d
    mpi
    2thd
    @5
    wps
    @1
    @8
    @2
    @5
    wps
    @10
    @1
    @5
    @9
    wps
    @9
    wps
    wph
    wb
    @5
    @3
    wph
    wps
    bicom
    wps
    wph
    bibif
    syl5bb
    con2bid
    @11
    syl6bb
    wph
    wps
    biorf
    @5
    @0
    wn
    @1
    @2
    wb
    @0
    wph
    wph
    wps
    simpl
    con3i
    @0
    @1
    biorf
    syl
    3bitr3d
    pm2.61i
    @0
    @4
    @6
    3orass
    3bitr4i
end
