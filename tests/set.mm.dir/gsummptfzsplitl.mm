include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "csn.mm"
include "fzfid.mm"
include "cin.mm"
include "caddc.mm"
include "c0.mm"
include "wceq.mm"
include "incom.mm"
include "a1i.mm"
include "1e0p1.mm"
include "oveq1i.mm"
include "ineq2d.mm"
include "cn0.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "elnn0uz.mm"
include "biimpi.mm"
include "fzpreddisj.mm"
include "3syl.mm"
include "3eqtrd.mm"
include "cun.mm"
include "fzpred.mm"
include "uncom.mm"
include "0p1e1.mm"
include "uneq1i.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "gsummptfidmsplit.mm"

theorem gsummptfzsplitl
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
  assume gsummptfzsplitl.y: |- ( ( ph /\ k e. ( 0 ... N ) ) -> Y e. B )

  disjoint B k
  disjoint N k
  disjoint k ph
  assert |- ( ph -> ( G gsum ( k e. ( 0 ... N ) |-> Y ) ) = ( ( G gsum ( k e. ( 1 ... N ) |-> Y ) ) .+ ( G gsum ( k e. { 0 } |-> Y ) ) ) )

  proof
    wph
    cc0
    cN
    cfz
    co
    #
    cB
    c1
    cN
    cfz
    co
    #
    cc0
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
    cN
    fzfid
    gsummptfzsplitl.y
    wph
    @1
    @2
    cin
    #
    @2
    @1
    cin
    #
    @2
    cc0
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cin
    #
    c0
    @3
    @4
    wceq
    wph
    @1
    @2
    incom
    a1i
    wph
    @1
    @6
    @2
    @1
    @6
    wceq
    wph
    c1
    @5
    cN
    cfz
    1e0p1
    oveq1i
    a1i
    ineq2d
    wph
    cN
    cn0
    wcel
    #
    cN
    cc0
    cuz
    cfv
    wcel
    #
    @7
    c0
    wceq
    gsummptfzsplit.n
    @8
    @9
    cN
    elnn0uz
    biimpi
    #
    cc0
    cN
    fzpreddisj
    3syl
    3eqtrd
    wph
    @0
    @2
    @6
    cun
    #
    @1
    @2
    cun
    #
    wph
    @8
    @9
    @0
    @11
    wceq
    gsummptfzsplit.n
    @10
    cc0
    cN
    fzpred
    3syl
    @11
    @6
    @2
    cun
    @12
    @2
    @6
    uncom
    @6
    @1
    @2
    @5
    c1
    cN
    cfz
    0p1e1
    oveq1i
    uneq1i
    eqtri
    syl6eq
    gsummptfidmsplit
end
