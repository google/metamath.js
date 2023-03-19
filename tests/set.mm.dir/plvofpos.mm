include "wa.mm"
include "pm3.2i.mm"
include "bicomi.mm"
include "biimpi.mm"
include "ax-mp.mm"

theorem plvofpos
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let wmu: wff mu
  let vk: setvar k
  let vx: setvar x
  assume plvofpos.1: |- ( ch <-> ( -. ph /\ -. ps ) )
  assume plvofpos.2: |- ( th <-> ( -. ph /\ ps ) )
  assume plvofpos.3: |- ( ta <-> ( ph /\ -. ps ) )
  assume plvofpos.4: |- ( et <-> ( ph /\ ps ) )
  assume plvofpos.5: |- ( ze <-> ( ( ( ( ( -. ( ( mu -> ch ) /\ ( mu -> th ) ) /\ -. ( ( mu -> ch ) /\ ( mu -> ta ) ) ) /\ -. ( ( mu -> ch ) /\ ( ch -> et ) ) ) /\ -. ( ( mu -> th ) /\ ( mu -> ta ) ) ) /\ -. ( ( mu -> th ) /\ ( mu -> et ) ) ) /\ -. ( ( mu -> ta ) /\ ( mu -> et ) ) ) )
  assume plvofpos.6: |- ( si <-> ( ( ( mu -> ch ) \/ ( mu -> th ) ) \/ ( ( mu -> ta ) \/ ( mu -> et ) ) ) )
  assume plvofpos.7: |- ( rh <-> ( ze /\ si ) )
  assume plvofpos.8: |- ze
  assume plvofpos.9: |- si


  assert |- rh

  proof
    wze
    wsi
    wa
    #
    wrh
    wze
    wsi
    plvofpos.8
    plvofpos.9
    pm3.2i
    @0
    wrh
    wrh
    @0
    plvofpos.7
    bicomi
    biimpi
    ax-mp
end
