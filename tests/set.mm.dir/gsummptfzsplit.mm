include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "csn.mm"
include "fzfid.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "fzp1disj.mm"
include "a1i.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cun.mm"
include "cn0.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "fzsuc.mm"
include "syl.mm"
include "gsummptfidmsplit.mm"

theorem gsummptfzsplit
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let vk: setvar k
  let cG: class G
  let cN: class N
  let cY: class Y
  assume gsummptfzsplit.b: |- B = ( Base ` G )
  assume gsummptfzsplit.p: |- .+ = ( +g ` G )
  assume gsummptfzsplit.g: |- ( ph -> G e. CMnd )
  assume gsummptfzsplit.n: |- ( ph -> N e. NN0 )
  assume gsummptfzsplit.y: |- ( ( ph /\ k e. ( 0 ... ( N + 1 ) ) ) -> Y e. B )

  disjoint B k
  disjoint N k
  disjoint k ph
  assert |- ( ph -> ( G gsum ( k e. ( 0 ... ( N + 1 ) ) |-> Y ) ) = ( ( G gsum ( k e. ( 0 ... N ) |-> Y ) ) .+ ( G gsum ( k e. { ( N + 1 ) } |-> Y ) ) ) )

  proof
    wph
    cc0
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    cB
    cc0
    cN
    cfz
    co
    #
    @0
    csn
    #
    c.pl
    vk
    cG
    cY
    gsummptfzsplit.b
    gsummptfzsplit.p
    gsummptfzsplit.g
    wph
    cc0
    @0
    fzfid
    gsummptfzsplit.y
    @2
    @3
    cin
    c0
    wceq
    wph
    cc0
    cN
    fzp1disj
    a1i
    wph
    cN
    cc0
    cuz
    cfv
    wcel
    #
    @1
    @2
    @3
    cun
    wceq
    wph
    cN
    cn0
    wcel
    @4
    gsummptfzsplit.n
    cN
    elnn0uz
    sylib
    cc0
    cN
    fzsuc
    syl
    gsummptfidmsplit
end
