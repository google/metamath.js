include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "ce.mm"
include "co.mm"
include "reeflog.mm"
include "oveqan12d.mm"
include "fveq2d.mm"
include "cr.mm"
include "wceq.mm"
include "relogcl.mm"
include "cc.mm"
include "recn.mm"
include "syl2an.mm"
include "relogef.mm"
include "syl.mm"
include "eqtr3d.mm"

theorem relogoprlem
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  assume relogoprlem.1: |- ( ( ( log ` A ) e. CC /\ ( log ` B ) e. CC ) -> ( exp ` ( ( log ` A ) F ( log ` B ) ) ) = ( ( exp ` ( log ` A ) ) G ( exp ` ( log ` B ) ) ) )
  assume relogoprlem.2: |- ( ( ( log ` A ) e. RR /\ ( log ` B ) e. RR ) -> ( ( log ` A ) F ( log ` B ) ) e. RR )


  assert |- ( ( A e. RR+ /\ B e. RR+ ) -> ( log ` ( A G B ) ) = ( ( log ` A ) F ( log ` B ) ) )

  proof
    cA
    crp
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cA
    clog
    cfv
    #
    ce
    cfv
    #
    cB
    clog
    cfv
    #
    ce
    cfv
    #
    cG
    co
    #
    clog
    cfv
    #
    cA
    cB
    cG
    co
    #
    clog
    cfv
    @3
    @5
    cF
    co
    #
    @2
    @7
    @9
    clog
    @0
    @1
    @4
    cA
    @6
    cB
    cG
    cA
    reeflog
    cB
    reeflog
    oveqan12d
    fveq2d
    @0
    @3
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @8
    @10
    wceq
    @1
    cA
    relogcl
    cB
    relogcl
    @11
    @12
    wa
    #
    @10
    ce
    cfv
    #
    clog
    cfv
    #
    @8
    @10
    @11
    @3
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @15
    @8
    wceq
    @12
    @3
    recn
    @5
    recn
    @16
    @17
    wa
    @14
    @7
    clog
    relogoprlem.1
    fveq2d
    syl2an
    @13
    @10
    cr
    wcel
    @15
    @10
    wceq
    relogoprlem.2
    @10
    relogef
    syl
    eqtr3d
    syl2an
    eqtr3d
end
