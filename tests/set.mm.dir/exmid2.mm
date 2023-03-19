include "wa.mm"
include "simpl.mm"
include "anim2i.mm"
include "ancoms.mm"
include "syl.mm"
include "wn.mm"
include "simpr.mm"
include "pm2.61dan.mm"

theorem exmid2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wet: wff et
  assume exmid2.1: |- ( ( ps /\ ph ) -> ch )
  assume exmid2.2: |- ( ( -. ps /\ et ) -> ch )


  assert |- ( ( ph /\ et ) -> ch )

  proof
    wph
    wet
    wa
    #
    wps
    wch
    @0
    wps
    wa
    wps
    wph
    wa
    #
    wch
    wps
    @0
    @1
    @0
    wph
    wps
    wph
    wet
    simpl
    anim2i
    ancoms
    exmid2.1
    syl
    @0
    wps
    wn
    #
    wa
    @2
    wet
    wa
    #
    wch
    @2
    @0
    @3
    @0
    wet
    @2
    wph
    wet
    simpr
    anim2i
    ancoms
    exmid2.2
    syl
    pm2.61dan
end
