include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "cof.mm"
include "co.mm"
include "ccoe.mm"
include "wceq.mm"
include "cdgr.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "eqid.mm"
include "coeaddlem.mm"
include "simprd.mm"

theorem dgradd
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  assume dgradd.1: |- M = ( deg ` F )
  assume dgradd.2: |- N = ( deg ` G )


  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) ) -> ( deg ` ( F oF + G ) ) <_ if ( M <_ N , N , M ) )

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
    caddc
    cof
    #
    co
    #
    ccoe
    cfv
    cF
    ccoe
    cfv
    #
    cG
    ccoe
    cfv
    #
    @1
    co
    wceq
    @2
    cdgr
    cfv
    cM
    cN
    cle
    wbr
    cN
    cM
    cif
    cle
    wbr
    @3
    @4
    cS
    cF
    cG
    cM
    cN
    @3
    eqid
    @4
    eqid
    dgradd.1
    dgradd.2
    coeaddlem
    simprd
end
