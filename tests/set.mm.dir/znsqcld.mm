include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wn.mm"
include "cn.mm"
include "wcel.mm"
include "zcnd.mm"
include "cz.mm"
include "2z.mm"
include "a1i.mm"
include "expne0d.mm"
include "neneqd.mm"
include "cn0.mm"
include "wo.mm"
include "zsqcl2.mm"
include "syl.mm"
include "elnn0.mm"
include "sylib.mm"
include "orcomd.mm"
include "ord.mm"
include "mpd.mm"

theorem znsqcld
  let wph: wff ph
  let cN: class N
  assume znsqcld.1: |- ( ph -> N e. ZZ )
  assume znsqcld.2: |- ( ph -> N =/= 0 )


  assert |- ( ph -> ( N ^ 2 ) e. NN )

  proof
    wph
    cN
    c2
    cexp
    co
    #
    cc0
    wceq
    #
    wn
    @0
    cn
    wcel
    #
    wph
    @0
    cc0
    wph
    cN
    c2
    wph
    cN
    znsqcld.1
    zcnd
    znsqcld.2
    c2
    cz
    wcel
    wph
    2z
    a1i
    expne0d
    neneqd
    wph
    @1
    @2
    wph
    @2
    @1
    wph
    @0
    cn0
    wcel
    #
    @2
    @1
    wo
    wph
    cN
    cz
    wcel
    @3
    znsqcld.1
    cN
    zsqcl2
    syl
    @0
    elnn0
    sylib
    orcomd
    ord
    mpd
end
