include "cz.mm"
include "wcel.mm"
include "zring.mm"
include "crg.mm"
include "csn.mm"
include "wss.mm"
include "cfv.mm"
include "clidl.mm"
include "zringring.mm"
include "snssi.mm"
include "zringbas.mm"
include "eqid.mm"
include "rspcl.mm"
include "sylancr.mm"

theorem znlidl
  let cS: class S
  let cN: class N
  let vf: setvar f
  let vn: setvar n
  let vs: setvar s
  let vz: setvar z
  let c.le: class .<_
  let cU: class U
  assume znval.s: |- S = ( RSpan ` ZZring )


  assert |- ( N e. ZZ -> ( S ` { N } ) e. ( LIdeal ` ZZring ) )

  proof
    cN
    cz
    wcel
    zring
    crg
    wcel
    cN
    csn
    #
    cz
    wss
    @0
    cS
    cfv
    zring
    clidl
    cfv
    #
    wcel
    zringring
    cN
    cz
    snssi
    cz
    zring
    @1
    @0
    cS
    znval.s
    zringbas
    @1
    eqid
    rspcl
    sylancr
end
