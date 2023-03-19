include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "cc0.mm"
include "wrex.mm"
include "wi.mm"
include "w3a.mm"
include "cz.mm"
include "eqid.mm"
include "0zd.mm"
include "lmbr2.mm"
include "wb.mm"
include "0z.mm"
include "rexuz3.mm"
include "ax-mp.mm"
include "imbi2i.mm"
include "ralbii.mm"
include "3anbi3i.mm"
include "syl6bb.mm"

theorem lmbr3v
  let wph: wff ph
  let vu: setvar u
  let cP: class P
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cX: class X
  assume lmbr3v.1: |- ( ph -> J e. ( TopOn ` X ) )

  disjoint F j
  disjoint F k
  disjoint F u
  disjoint j k
  disjoint j u
  disjoint k u
  disjoint J j
  disjoint J k
  disjoint J u
  disjoint P j
  disjoint P k
  disjoint P u
  disjoint X j
  disjoint X k
  disjoint X u
  disjoint j ph
  disjoint k ph
  disjoint ph u
  assert |- ( ph -> ( F ( ~~>t ` J ) P <-> ( F e. ( X ^pm CC ) /\ P e. X /\ A. u e. J ( P e. u -> E. j e. ZZ A. k e. ( ZZ>= ` j ) ( k e. dom F /\ ( F ` k ) e. u ) ) ) ) )

  proof
    wph
    cF
    cP
    cJ
    clm
    cfv
    wbr
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    cP
    cX
    wcel
    #
    cP
    vu
    cv
    #
    wcel
    #
    vk
    cv
    #
    cF
    cdm
    wcel
    @4
    cF
    cfv
    @2
    wcel
    wa
    #
    vk
    vj
    cv
    cuz
    cfv
    wral
    #
    vj
    cc0
    cuz
    cfv
    #
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    w3a
    @0
    @1
    @3
    @6
    vj
    cz
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    w3a
    wph
    vu
    cP
    vj
    vk
    cF
    cJ
    cc0
    cX
    @7
    lmbr3v.1
    @7
    eqid
    #
    wph
    0zd
    lmbr2
    @10
    @13
    @0
    @1
    @9
    @12
    vu
    cJ
    @8
    @11
    @3
    cc0
    cz
    wcel
    @8
    @11
    wb
    0z
    @5
    vj
    vk
    cc0
    @7
    @14
    rexuz3
    ax-mp
    imbi2i
    ralbii
    3anbi3i
    syl6bb
end
