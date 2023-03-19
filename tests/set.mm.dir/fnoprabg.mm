include "weu.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "coprab.mm"
include "wfun.mm"
include "cdm.mm"
include "copab.mm"
include "wceq.mm"
include "wfn.mm"
include "wmo.mm"
include "eumo.mm"
include "imim2i.mm"
include "moanimv.mm"
include "sylibr.mm"
include "2alimi.mm"
include "funoprabg.mm"
include "syl.mm"
include "wex.mm"
include "dmoprab.mm"
include "nfa1.mm"
include "nfa2.mm"
include "wb.mm"
include "simpl.mm"
include "exlimiv.mm"
include "euex.mm"
include "ancld.mm"
include "19.42v.mm"
include "syl6ibr.mm"
include "impbid2.mm"
include "sps.mm"
include "opabbid.mm"
include "syl5eq.mm"
include "df-fn.mm"
include "sylanbrc.mm"

theorem fnoprabg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( A. x A. y ( ph -> E! z ps ) -> { <. <. x , y >. , z >. | ( ph /\ ps ) } Fn { <. x , y >. | ph } )

  proof
    wph
    wps
    vz
    weu
    #
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    wph
    wps
    wa
    #
    vx
    vy
    vz
    coprab
    #
    wfun
    #
    @5
    cdm
    #
    wph
    vx
    vy
    copab
    #
    wceq
    @5
    @8
    wfn
    @3
    @4
    vz
    wmo
    #
    vy
    wal
    vx
    wal
    @6
    @1
    @9
    vx
    vy
    @1
    wph
    wps
    vz
    wmo
    #
    wi
    @9
    @0
    @10
    wph
    wps
    vz
    eumo
    imim2i
    wph
    wps
    vz
    moanimv
    sylibr
    2alimi
    @4
    vx
    vy
    vz
    funoprabg
    syl
    @3
    @7
    @4
    vz
    wex
    #
    vx
    vy
    copab
    @8
    @4
    vx
    vy
    vz
    dmoprab
    @3
    @11
    wph
    vx
    vy
    @2
    vx
    nfa1
    @1
    vy
    vx
    nfa2
    @2
    @11
    wph
    wb
    #
    vx
    @1
    @12
    vy
    @1
    @11
    wph
    @4
    wph
    vz
    wph
    wps
    simpl
    exlimiv
    @1
    wph
    wph
    wps
    vz
    wex
    #
    wa
    @11
    @1
    wph
    @13
    @0
    @13
    wph
    wps
    vz
    euex
    imim2i
    ancld
    wph
    wps
    vz
    19.42v
    syl6ibr
    impbid2
    sps
    sps
    opabbid
    syl5eq
    @5
    @8
    df-fn
    sylanbrc
end
