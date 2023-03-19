include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cv.mm"
include "cmin.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmul.mm"
include "cmpt.mm"
include "cc.mm"
include "ccncf.mm"
include "cibl.mm"
include "renegcl.mm"
include "adantr.mm"
include "simpl.mm"
include "wss.mm"
include "2cnd.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "ssid.mm"
include "a1i.mm"
include "cncfmptc.mm"
include "syl3anc.mm"
include "areacirclem2.mm"
include "mulcncf.mm"
include "cnicciblnc.mm"

theorem areacirclem3
  let vt: setvar t
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vv: setvar v
  let cS: class S

  disjoint R t
  disjoint x y
  disjoint t x
  disjoint u x
  disjoint v x
  disjoint R x
  disjoint t y
  disjoint u y
  disjoint v y
  disjoint R y
  disjoint t u
  disjoint t v
  disjoint u v
  disjoint R u
  disjoint R v
  disjoint S t
  disjoint S u
  disjoint S v
  assert |- ( ( R e. RR /\ 0 <_ R ) -> ( t e. ( -u R [,] R ) |-> ( 2 x. ( sqrt ` ( ( R ^ 2 ) - ( t ^ 2 ) ) ) ) ) e. L^1 )

  proof
    cR
    cr
    wcel
    #
    cc0
    cR
    cle
    wbr
    #
    wa
    #
    cR
    cneg
    #
    cr
    wcel
    #
    @0
    vt
    @3
    cR
    cicc
    co
    #
    c2
    cR
    c2
    cexp
    co
    vt
    cv
    c2
    cexp
    co
    cmin
    co
    csqrt
    cfv
    #
    cmul
    co
    cmpt
    #
    @5
    cc
    ccncf
    co
    #
    wcel
    @7
    cibl
    wcel
    @0
    @4
    @1
    cR
    renegcl
    adantr
    #
    @0
    @1
    simpl
    #
    @2
    vt
    c2
    @6
    @5
    @2
    c2
    cc
    wcel
    @5
    cc
    wss
    cc
    cc
    wss
    #
    vt
    @5
    c2
    cmpt
    @8
    wcel
    @2
    2cnd
    @2
    @5
    cr
    cc
    @2
    @4
    @0
    @5
    cr
    wss
    @9
    @10
    @3
    cR
    iccssre
    syl2anc
    ax-resscn
    syl6ss
    @11
    @2
    cc
    ssid
    a1i
    vt
    c2
    @5
    cc
    cncfmptc
    syl3anc
    vt
    cR
    areacirclem2
    mulcncf
    @3
    cR
    @7
    cnicciblnc
    syl3anc
end
