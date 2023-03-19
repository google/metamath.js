include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "con0.mm"
include "cha.mm"
include "wcel.mm"
include "wss.mm"
include "1on.mm"
include "2on.mm"
include "prssi.mm"
include "mp2an.mm"
include "c0.mm"
include "cpw.mm"
include "csn.mm"
include "df1o2.mm"
include "pw0.mm"
include "eqtr4i.mm"
include "cvv.mm"
include "0ex.mm"
include "dishaus.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "df2o2.mm"
include "pwpw0.mm"
include "p0ex.mm"
include "ssini.mm"

theorem ssoninhaus



  assert |- { 1o , 2o } C_ ( On i^i Haus )

  proof
    c1o
    c2o
    cpr
    #
    con0
    cha
    c1o
    con0
    wcel
    c2o
    con0
    wcel
    @0
    con0
    wss
    1on
    2on
    c1o
    c2o
    con0
    prssi
    mp2an
    c1o
    cha
    wcel
    c2o
    cha
    wcel
    @0
    cha
    wss
    c1o
    c0
    cpw
    #
    cha
    c1o
    c0
    csn
    #
    @1
    df1o2
    pw0
    eqtr4i
    c0
    cvv
    wcel
    @1
    cha
    wcel
    0ex
    c0
    cvv
    dishaus
    ax-mp
    eqeltri
    c2o
    @2
    cpw
    #
    cha
    c2o
    c0
    @2
    cpr
    @3
    df2o2
    pwpw0
    eqtr4i
    @2
    cvv
    wcel
    @3
    cha
    wcel
    p0ex
    @2
    cvv
    dishaus
    ax-mp
    eqeltri
    c1o
    c2o
    cha
    prssi
    mp2an
    ssini
end
