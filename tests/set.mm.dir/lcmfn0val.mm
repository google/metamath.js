include "cz.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "cc0.mm"
include "wnel.mm"
include "w3a.mm"
include "clcmf.mm"
include "cfv.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "wceq.mm"
include "lcmfval.mm"
include "3adant3.mm"
include "wn.mm"
include "df-nel.mm"
include "iffalse.mm"
include "sylbi.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"

theorem lcmfn0val
  let vm: setvar m
  let vn: setvar n
  let cZ: class Z
  let vz: setvar z

  disjoint Z m
  disjoint Z n
  disjoint m n
  disjoint Z z
  disjoint m z
  disjoint n z
  assert |- ( ( Z C_ ZZ /\ Z e. Fin /\ 0 e/ Z ) -> ( _lcm ` Z ) = inf ( { n e. NN | A. m e. Z m || n } , RR , < ) )

  proof
    cZ
    cz
    wss
    #
    cZ
    cfn
    wcel
    #
    cc0
    cZ
    wnel
    #
    w3a
    cZ
    clcmf
    cfv
    #
    cc0
    cZ
    wcel
    #
    cc0
    vm
    cv
    vn
    cv
    cdvds
    wbr
    vm
    cZ
    wral
    vn
    cn
    crab
    cr
    clt
    cinf
    #
    cif
    #
    @5
    @0
    @1
    @3
    @6
    wceq
    @2
    vm
    vn
    cZ
    lcmfval
    3adant3
    @2
    @0
    @6
    @5
    wceq
    #
    @1
    @2
    @4
    wn
    @7
    cc0
    cZ
    df-nel
    @4
    cc0
    @5
    iffalse
    sylbi
    3ad2ant3
    eqtrd
end
