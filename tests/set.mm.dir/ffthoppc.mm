include "ctpos.mm"
include "cful.mm"
include "co.mm"
include "wbr.mm"
include "cfth.mm"
include "cin.mm"
include "wa.mm"
include "brin.mm"
include "sylib.mm"
include "simpld.mm"
include "fulloppc.mm"
include "simprd.mm"
include "fthoppc.mm"
include "sylanbrc.mm"

theorem ffthoppc
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cP: class P
  let cF: class F
  let cG: class G
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  assume fulloppc.o: |- O = ( oppCat ` C )
  assume fulloppc.p: |- P = ( oppCat ` D )
  assume ffthoppc.f: |- ( ph -> F ( ( C Full D ) i^i ( C Faith D ) ) G )


  assert |- ( ph -> F ( ( O Full P ) i^i ( O Faith P ) ) tpos G )

  proof
    wph
    cF
    cG
    ctpos
    #
    cO
    cP
    cful
    co
    #
    wbr
    cF
    @0
    cO
    cP
    cfth
    co
    #
    wbr
    cF
    @0
    @1
    @2
    cin
    wbr
    wph
    cC
    cD
    cP
    cF
    cG
    cO
    fulloppc.o
    fulloppc.p
    wph
    cF
    cG
    cC
    cD
    cful
    co
    #
    wbr
    #
    cF
    cG
    cC
    cD
    cfth
    co
    #
    wbr
    #
    wph
    cF
    cG
    @3
    @5
    cin
    wbr
    @4
    @6
    wa
    ffthoppc.f
    cF
    cG
    @3
    @5
    brin
    sylib
    #
    simpld
    fulloppc
    wph
    cC
    cD
    cP
    cF
    cG
    cO
    fulloppc.o
    fulloppc.p
    wph
    @4
    @6
    @7
    simprd
    fthoppc
    cF
    @0
    @1
    @2
    brin
    sylanbrc
end
