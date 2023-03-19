include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "readdcld.mm"
include "recnd.mm"
include "addcomd.mm"
include "leadd1dd.mm"
include "eqbrtrd.mm"
include "letrd.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "leaddsub.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem lesub3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )
  assume lesub3d.x: |- ( ph -> X e. RR )
  assume lesub3d.g: |- ( ph -> ( X + C ) <_ A )
  assume lesub3d.l: |- ( ph -> B <_ X )


  assert |- ( ph -> C <_ ( A - B ) )

  proof
    wph
    cC
    cB
    caddc
    co
    #
    cA
    cle
    wbr
    #
    cC
    cA
    cB
    cmin
    co
    cle
    wbr
    #
    wph
    @0
    cX
    cC
    caddc
    co
    #
    cA
    wph
    cC
    cB
    ltadd1d.3
    ltnegd.2
    readdcld
    wph
    cX
    cC
    lesub3d.x
    ltadd1d.3
    readdcld
    leidd.1
    wph
    @0
    cB
    cC
    caddc
    co
    @3
    cle
    wph
    cC
    cB
    wph
    cC
    ltadd1d.3
    recnd
    wph
    cB
    ltnegd.2
    recnd
    addcomd
    wph
    cB
    cX
    cC
    ltnegd.2
    lesub3d.x
    ltadd1d.3
    lesub3d.l
    leadd1dd
    eqbrtrd
    lesub3d.g
    letrd
    wph
    cC
    cr
    wcel
    cB
    cr
    wcel
    cA
    cr
    wcel
    @1
    @2
    wb
    ltadd1d.3
    ltnegd.2
    leidd.1
    cC
    cB
    cA
    leaddsub
    syl3anc
    mpbid
end
