include "wo.mm"
include "wn.mm"
include "rblem1.mm"
include "rb-ax2.mm"
include "rb-ax1.mm"
include "anmp.mm"
include "rbsyl.mm"
include "rb-ax4.mm"
include "rblem2.mm"
include "rb-ax3.mm"

theorem rblem4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume rblem4.1: |- ( -. ph \/ th )
  assume rblem4.2: |- ( -. ps \/ ta )
  assume rblem4.3: |- ( -. ch \/ et )


  assert |- ( -. ( ( ph \/ ps ) \/ ch ) \/ ( ( et \/ ta ) \/ th ) )

  proof
    wph
    wps
    wo
    #
    wch
    wo
    wn
    #
    wch
    wps
    wo
    #
    wph
    wo
    #
    wet
    wta
    wo
    #
    wth
    wo
    @2
    @4
    wph
    wth
    wch
    wet
    wps
    wta
    rblem4.3
    rblem4.2
    rblem1
    rblem4.1
    rblem1
    @1
    wps
    wch
    wo
    #
    wph
    wo
    #
    @3
    @6
    wn
    #
    wph
    @2
    wo
    #
    @3
    wph
    @2
    rb-ax2
    @7
    wph
    @5
    wo
    #
    @8
    @5
    wn
    @2
    wo
    @9
    wn
    @8
    wo
    wps
    wch
    rb-ax2
    wph
    @5
    @2
    rb-ax1
    anmp
    @5
    wph
    rb-ax2
    rbsyl
    rbsyl
    @1
    @6
    @6
    wo
    @6
    @6
    rb-ax4
    @0
    @6
    wch
    @6
    @0
    wn
    @9
    @6
    wph
    @5
    rb-ax2
    wps
    wch
    wph
    rblem2
    rbsyl
    wch
    wn
    #
    @5
    wo
    @10
    @6
    wo
    wch
    wps
    rb-ax3
    @5
    wph
    @10
    rblem2
    anmp
    rblem1
    rbsyl
    rbsyl
    rbsyl
end
