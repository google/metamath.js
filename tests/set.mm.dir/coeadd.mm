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
include "simpld.mm"

theorem coeadd
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let cN: class N
  assume coefv0.1: |- A = ( coeff ` F )
  assume coeadd.2: |- B = ( coeff ` G )


  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) ) -> ( coeff ` ( F oF + G ) ) = ( A oF + B ) )

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
    cA
    cB
    @1
    co
    wceq
    @2
    cdgr
    cfv
    cF
    cdgr
    cfv
    #
    cG
    cdgr
    cfv
    #
    cle
    wbr
    @4
    @3
    cif
    cle
    wbr
    cA
    cB
    cS
    cF
    cG
    @3
    @4
    coefv0.1
    coeadd.2
    @3
    eqid
    @4
    eqid
    coeaddlem
    simpld
end
