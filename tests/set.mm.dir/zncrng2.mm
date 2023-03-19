include "cz.mm"
include "wcel.mm"
include "zring.mm"
include "ccrg.mm"
include "csn.mm"
include "cfv.mm"
include "clidl.mm"
include "zringcrng.mm"
include "znlidl.mm"
include "eqid.mm"
include "quscrng.mm"
include "sylancr.mm"

theorem zncrng2
  let cS: class S
  let cU: class U
  let cN: class N
  let vf: setvar f
  let vn: setvar n
  let vs: setvar s
  let vz: setvar z
  let c.le: class .<_
  assume znval.s: |- S = ( RSpan ` ZZring )
  assume znval.u: |- U = ( ZZring /s ( ZZring ~QG ( S ` { N } ) ) )


  assert |- ( N e. ZZ -> U e. CRing )

  proof
    cN
    cz
    wcel
    zring
    ccrg
    wcel
    cN
    csn
    cS
    cfv
    #
    zring
    clidl
    cfv
    #
    wcel
    cU
    ccrg
    wcel
    zringcrng
    cS
    cN
    znval.s
    znlidl
    zring
    @0
    cU
    @1
    znval.u
    @1
    eqid
    quscrng
    sylancr
end
