include "weu.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "coprab.mm"
include "copab.mm"
include "wfn.mm"
include "gen2.mm"
include "fnoprabg.mm"
include "ax-mp.mm"

theorem fnoprab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume fnoprab.1: |- ( ph -> E! z ps )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- { <. <. x , y >. , z >. | ( ph /\ ps ) } Fn { <. x , y >. | ph }

  proof
    wph
    wps
    vz
    weu
    wi
    #
    vy
    wal
    vx
    wal
    wph
    wps
    wa
    vx
    vy
    vz
    coprab
    wph
    vx
    vy
    copab
    wfn
    @0
    vx
    vy
    fnoprab.1
    gen2
    wph
    wps
    vx
    vy
    vz
    fnoprabg
    ax-mp
end
