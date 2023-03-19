include "cprod.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "difssd.mm"
include "cv.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "eldifi.mm"
include "adantr.mm"
include "adantl.mm"
include "mulcld.mm"
include "wceq.mm"
include "eldifsni.mm"
include "mulne0d.mm"
include "neneqd.mm"
include "ovex.mm"
include "elsn.mm"
include "sylnibr.mm"
include "eldifd.mm"
include "wb.mm"
include "elsng.mm"
include "syl.mm"
include "mtbird.mm"
include "c1.mm"
include "wn.mm"
include "ax-1cn.mm"
include "0ne1.mm"
include "necomi.mm"
include "neneq.mm"
include "ax-mp.mm"
include "1ex.mm"
include "mtbir.mm"
include "pm3.2i.mm"
include "eldif.mm"
include "mpbir.mm"
include "a1i.mm"
include "fprodcllemf.mm"

theorem fprodn0f
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fprodn0f.kph: |- F/ k ph
  assume fprodn0f.a: |- ( ph -> A e. Fin )
  assume fprodn0f.b: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fprodn0f.bne0: |- ( ( ph /\ k e. A ) -> B =/= 0 )

  disjoint A k
  disjoint A x
  disjoint A y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> prod_ k e. A B =/= 0 )

  proof
    wph
    cA
    cB
    vk
    cprod
    #
    cc
    cc0
    csn
    #
    cdif
    #
    wcel
    @0
    cc0
    wne
    wph
    vx
    vy
    cA
    cB
    @2
    vk
    fprodn0f.kph
    wph
    cc
    @1
    difssd
    vx
    cv
    #
    @2
    wcel
    #
    vy
    cv
    #
    @2
    wcel
    #
    wa
    #
    @3
    @5
    cmul
    co
    #
    @2
    wcel
    wph
    @7
    @8
    cc
    @1
    @7
    @3
    @5
    @4
    @3
    cc
    wcel
    @6
    @3
    cc
    @1
    eldifi
    adantr
    #
    @6
    @5
    cc
    wcel
    @4
    @5
    cc
    @1
    eldifi
    adantl
    #
    mulcld
    @7
    @8
    cc0
    wceq
    @8
    @1
    wcel
    @7
    @8
    cc0
    @7
    @3
    @5
    @9
    @10
    @4
    @3
    cc0
    wne
    @6
    @3
    cc
    cc0
    eldifsni
    adantr
    @6
    @5
    cc0
    wne
    @4
    @5
    cc
    cc0
    eldifsni
    adantl
    mulne0d
    neneqd
    @8
    cc0
    @3
    @5
    cmul
    ovex
    elsn
    sylnibr
    eldifd
    adantl
    fprodn0f.a
    wph
    vk
    cv
    cA
    wcel
    wa
    #
    cB
    cc
    @1
    fprodn0f.b
    @11
    cB
    @1
    wcel
    #
    cB
    cc0
    wceq
    #
    @11
    cB
    cc0
    fprodn0f.bne0
    neneqd
    @11
    cB
    cc
    wcel
    @12
    @13
    wb
    fprodn0f.b
    cB
    cc0
    cc
    elsng
    syl
    mtbird
    eldifd
    c1
    @2
    wcel
    #
    wph
    @14
    c1
    cc
    wcel
    #
    c1
    @1
    wcel
    #
    wn
    #
    wa
    @15
    @17
    ax-1cn
    @16
    c1
    cc0
    wceq
    #
    c1
    cc0
    wne
    @18
    wn
    cc0
    c1
    0ne1
    necomi
    c1
    cc0
    neneq
    ax-mp
    c1
    cc0
    1ex
    elsn
    mtbir
    pm3.2i
    c1
    cc
    @1
    eldif
    mpbir
    a1i
    fprodcllemf
    @0
    cc
    cc0
    eldifsni
    syl
end
