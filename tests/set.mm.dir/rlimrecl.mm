include "cr.mm"
include "cv.mm"
include "cim.mm"
include "cfv.mm"
include "cabs.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "eldifi.mm"
include "adantl.mm"
include "imcld.mm"
include "recnd.mm"
include "wn.mm"
include "cc0.mm"
include "wne.mm"
include "eldifn.mm"
include "wceq.mm"
include "wb.mm"
include "reim0b.mm"
include "syl.mm"
include "necon3bbid.mm"
include "mpbid.mm"
include "absrpcld.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "adantr.mm"
include "simpr.mm"
include "subcld.mm"
include "absimle.mm"
include "imsubd.mm"
include "reim0.mm"
include "oveq2d.mm"
include "subid1d.mm"
include "3eqtrrd.mm"
include "fveq2d.mm"
include "abssubd.mm"
include "3brtr4d.mm"
include "rlimcld2.mm"

theorem rlimrecl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cD: class D
  let cR: class R
  assume rlimcld2.1: |- ( ph -> sup ( A , RR* , < ) = +oo )
  assume rlimcld2.2: |- ( ph -> ( x e. A |-> B ) ~~>r C )
  assume rlimrecl.3: |- ( ( ph /\ x e. A ) -> B e. RR )

  disjoint A x
  disjoint C x
  disjoint ph x
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint r w
  disjoint B r
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C r
  disjoint w x
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint ph r
  disjoint ph y
  disjoint ph z
  disjoint D r
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint R r
  disjoint R x
  disjoint R z
  assert |- ( ph -> C e. RR )

  proof
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    cr
    vy
    cv
    #
    cim
    cfv
    #
    cabs
    cfv
    #
    rlimcld2.1
    rlimcld2.2
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    wph
    @0
    cc
    cr
    cdif
    wcel
    #
    wa
    #
    @1
    @4
    @1
    @4
    @0
    @3
    @0
    cc
    wcel
    #
    wph
    @0
    cc
    cr
    eldifi
    adantl
    #
    imcld
    recnd
    #
    @4
    @0
    cr
    wcel
    #
    wn
    #
    @1
    cc0
    wne
    @3
    @9
    wph
    @0
    cc
    cr
    eldifn
    adantl
    @4
    @8
    @1
    cc0
    @4
    @5
    @8
    @1
    cc0
    wceq
    wb
    @6
    @0
    reim0b
    syl
    necon3bbid
    mpbid
    absrpcld
    @4
    vz
    cv
    #
    cr
    wcel
    #
    wa
    #
    @0
    @10
    cmin
    co
    #
    cim
    cfv
    #
    cabs
    cfv
    #
    @13
    cabs
    cfv
    #
    @2
    @10
    @0
    cmin
    co
    cabs
    cfv
    cle
    @12
    @13
    cc
    wcel
    @15
    @16
    cle
    wbr
    @12
    @0
    @10
    @4
    @5
    @11
    @6
    adantr
    #
    @12
    @10
    @4
    @11
    simpr
    recnd
    #
    subcld
    @13
    absimle
    syl
    @12
    @1
    @14
    cabs
    @12
    @14
    @1
    @10
    cim
    cfv
    #
    cmin
    co
    @1
    cc0
    cmin
    co
    @1
    @12
    @0
    @10
    @17
    @18
    imsubd
    @12
    @19
    cc0
    @1
    cmin
    @11
    @19
    cc0
    wceq
    @4
    @10
    reim0
    adantl
    oveq2d
    @12
    @1
    @4
    @1
    cc
    wcel
    @11
    @7
    adantr
    subid1d
    3eqtrrd
    fveq2d
    @12
    @10
    @0
    @18
    @17
    abssubd
    3brtr4d
    rlimrecl.3
    rlimcld2
end
