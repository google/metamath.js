include "wn.mm"
include "wi.mm"
include "jc.mm"
include "notnotb.mm"
include "imbi2i.mm"
include "sylnibr.mm"

theorem jcn
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume jcn.1: |- ( ph -> ps )
  assume jcn.2: |- ( ph -> -. ch )


  assert |- ( ph -> -. ( ps -> ch ) )

  proof
    wph
    wps
    wch
    wn
    #
    wn
    #
    wi
    wps
    wch
    wi
    wph
    wps
    @0
    jcn.1
    jcn.2
    jc
    wch
    @1
    wps
    wch
    notnotb
    imbi2i
    sylnibr
end
