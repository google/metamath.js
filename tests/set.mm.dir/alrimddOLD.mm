include "wal.mm"
include "nfrdOLD.mm"
include "alimdOLD.mm"
include "syld.mm"

theorem alrimddOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume alrimddOLD.1: |- nfOLD x ph
  assume alrimddOLD.2: |- ( ph -> nfOLD x ps )
  assume alrimddOLD.3: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps -> A. x ch ) )

  proof
    wph
    wps
    wps
    vx
    wal
    wch
    vx
    wal
    wph
    wps
    vx
    alrimddOLD.2
    nfrdOLD
    wph
    wps
    wch
    vx
    alrimddOLD.1
    alrimddOLD.3
    alimdOLD
    syld
end
