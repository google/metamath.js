include "cn.mm"
include "crepr.mm"
include "cfv.mm"
include "co.mm"
include "c1.mm"
include "cfz.mm"
include "cin.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "reprinfz1.mm"
include "wceq.mm"
include "fz1ssnn.mm"
include "dfss.mm"
include "mpbi.mm"
include "incom.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "syl6eqr.mm"

theorem reprfz1
  let wph: wff ph
  let cS: class S
  let cN: class N
  assume reprfz1.n: |- ( ph -> N e. NN0 )
  assume reprfz1.s: |- ( ph -> S e. NN0 )


  assert |- ( ph -> ( NN ( repr ` S ) N ) = ( ( 1 ... N ) ( repr ` S ) N ) )

  proof
    wph
    cn
    cN
    cS
    crepr
    cfv
    #
    co
    cn
    c1
    cN
    cfz
    co
    #
    cin
    #
    cN
    @0
    co
    @1
    cN
    @0
    co
    wph
    cn
    cS
    cN
    reprfz1.n
    reprfz1.s
    cn
    cn
    wss
    wph
    cn
    ssid
    a1i
    reprinfz1
    @1
    @2
    cN
    @0
    @1
    @1
    cn
    cin
    #
    @2
    @1
    cn
    wss
    @1
    @3
    wceq
    cN
    fz1ssnn
    @1
    cn
    dfss
    mpbi
    @1
    cn
    incom
    eqtri
    oveq1i
    syl6eqr
end
