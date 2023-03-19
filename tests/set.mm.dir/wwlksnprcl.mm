include "cword.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cwwlksn.mm"
include "cwwlks.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wb.mm"
include "iswwlksn.mm"
include "adantl.mm"
include "ccatws1lenp1b.mm"
include "biimpd.mm"
include "adantld.mm"
include "sylbid.mm"

theorem wwlksnprcl
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( W e. Word V /\ N e. NN0 ) -> ( ( W ++ <" X "> ) e. ( N WWalksN G ) -> ( # ` W ) = N ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cW
    cX
    cs1
    cconcat
    co
    #
    cN
    cG
    cwwlksn
    co
    wcel
    #
    @3
    cG
    cwwlks
    cfv
    wcel
    #
    @3
    chash
    cfv
    cN
    c1
    caddc
    co
    wceq
    #
    wa
    #
    cW
    chash
    cfv
    cN
    wceq
    #
    @1
    @4
    @7
    wb
    @0
    cG
    cN
    @3
    iswwlksn
    adantl
    @2
    @6
    @8
    @5
    @2
    @6
    @8
    cN
    cV
    cW
    cX
    ccatws1lenp1b
    biimpd
    adantld
    sylbid
end
