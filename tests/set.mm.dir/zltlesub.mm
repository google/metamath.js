include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "zred.mm"
include "readdcld.mm"
include "cr.mm"
include "wcel.mm"
include "peano2re.mm"
include "syl.mm"
include "recnd.mm"
include "npcand.mm"
include "breqtrrd.mm"
include "1red.mm"
include "ltadd2dd.mm"
include "lelttrd.mm"
include "cz.mm"
include "wb.mm"
include "zleltp1.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem zltlesub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cN: class N
  assume zltlesub.n: |- ( ph -> N e. ZZ )
  assume zltlesub.a: |- ( ph -> A e. RR )
  assume zltlesub.nlea: |- ( ph -> N <_ A )
  assume zltlesub.b: |- ( ph -> B e. RR )
  assume zltlesub.blt1: |- ( ph -> B < 1 )
  assume zltlesub.asb: |- ( ph -> ( A - B ) e. ZZ )


  assert |- ( ph -> N <_ ( A - B ) )

  proof
    wph
    cN
    cA
    cB
    cmin
    co
    #
    cle
    wbr
    #
    cN
    @0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wph
    cN
    @0
    cB
    caddc
    co
    #
    @2
    wph
    cN
    zltlesub.n
    zred
    wph
    @0
    cB
    wph
    @0
    zltlesub.asb
    zred
    #
    zltlesub.b
    readdcld
    wph
    @0
    cr
    wcel
    @2
    cr
    wcel
    @5
    @0
    peano2re
    syl
    wph
    cN
    cA
    @4
    cle
    zltlesub.nlea
    wph
    cA
    cB
    wph
    cA
    zltlesub.a
    recnd
    wph
    cB
    zltlesub.b
    recnd
    npcand
    breqtrrd
    wph
    cB
    c1
    @0
    zltlesub.b
    wph
    1red
    @5
    zltlesub.blt1
    ltadd2dd
    lelttrd
    wph
    cN
    cz
    wcel
    @0
    cz
    wcel
    @1
    @3
    wb
    zltlesub.n
    zltlesub.asb
    cN
    @0
    zleltp1
    syl2anc
    mpbird
end
