include "clfig.mm"
include "wcel.mm"
include "clnr.mm"
include "clnm.mm"
include "lnrfg.mm"
include "lnmlssfg.mm"
include "stoic3.mm"

theorem lnrfgtr
  let cP: class P
  let cS: class S
  let cU: class U
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b
  assume lnrfg.s: |- S = ( Scalar ` M )
  assume lnrfgtr.u: |- U = ( LSubSp ` M )
  assume lnrfgtr.n: |- N = ( M |`s P )


  assert |- ( ( M e. LFinGen /\ S e. LNoeR /\ P e. U ) -> N e. LFinGen )

  proof
    cM
    clfig
    wcel
    cS
    clnr
    wcel
    cM
    clnm
    wcel
    cP
    cU
    wcel
    cN
    clfig
    wcel
    cS
    cM
    lnrfg.s
    lnrfg
    cN
    cU
    cP
    cM
    lnrfgtr.u
    lnrfgtr.n
    lnmlssfg
    stoic3
end
