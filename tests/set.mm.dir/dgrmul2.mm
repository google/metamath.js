include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "ccoe.mm"
include "cn0.mm"
include "cc0.mm"
include "cv.mm"
include "cfz.mm"
include "cmin.mm"
include "csu.mm"
include "cmpt.mm"
include "wceq.mm"
include "cdgr.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "eqid.mm"
include "coemullem.mm"
include "simprd.mm"

theorem dgrmul2
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  assume dgradd.1: |- M = ( deg ` F )
  assume dgradd.2: |- N = ( deg ` G )


  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) ) -> ( deg ` ( F oF x. G ) ) <_ ( M + N ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    cG
    @0
    wcel
    wa
    cF
    cG
    cmul
    cof
    co
    #
    ccoe
    cfv
    vn
    cn0
    cc0
    vn
    cv
    #
    cfz
    co
    vk
    cv
    #
    cF
    ccoe
    cfv
    #
    cfv
    @2
    @3
    cmin
    co
    cG
    ccoe
    cfv
    #
    cfv
    cmul
    co
    vk
    csu
    cmpt
    wceq
    @1
    cdgr
    cfv
    cM
    cN
    caddc
    co
    cle
    wbr
    @4
    @5
    cS
    vk
    vn
    cF
    cG
    cM
    cN
    @4
    eqid
    @5
    eqid
    dgradd.1
    dgradd.2
    coemullem
    simprd
end
