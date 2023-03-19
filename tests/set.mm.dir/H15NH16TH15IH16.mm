include "wa.mm"
include "a1i.mm"

theorem H15NH16TH15IH16
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
  let wla: wff la
  let wka: wff ka
  let wjph: wff jph
  let wjps: wff jps
  let wjch: wff jch
  let wjth: wff jth
  let vk: setvar k
  let vx: setvar x
  assume H15NH16TH15IH16.1: |- ph
  assume H15NH16TH15IH16.2: |- ps
  assume H15NH16TH15IH16.3: |- ch
  assume H15NH16TH15IH16.4: |- th
  assume H15NH16TH15IH16.5: |- ta
  assume H15NH16TH15IH16.6: |- et
  assume H15NH16TH15IH16.7: |- ze
  assume H15NH16TH15IH16.8: |- si
  assume H15NH16TH15IH16.9: |- rh
  assume H15NH16TH15IH16.10: |- mu
  assume H15NH16TH15IH16.11: |- la
  assume H15NH16TH15IH16.12: |- ka
  assume H15NH16TH15IH16.13: |- jph
  assume H15NH16TH15IH16.14: |- jps
  assume H15NH16TH15IH16.15: |- jch
  assume H15NH16TH15IH16.16: |- jth


  assert |- ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) /\ jph ) /\ jps ) /\ jch ) -> jth )

  proof
    wjth
    wph
    wps
    wa
    wch
    wa
    wth
    wa
    wta
    wa
    wet
    wa
    wze
    wa
    wsi
    wa
    wrh
    wa
    wmu
    wa
    wla
    wa
    wka
    wa
    wjph
    wa
    wjps
    wa
    wjch
    wa
    H15NH16TH15IH16.16
    a1i
end
