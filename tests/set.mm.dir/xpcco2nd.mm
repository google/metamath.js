include "cop.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "cco.mm"
include "c2nd.mm"
include "wceq.mm"
include "eqid.mm"
include "xpcco.mm"
include "ovex.mm"
include "op2ndd.mm"
include "syl.mm"

theorem xpcco2nd
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume xpcco1st.t: |- T = ( C Xc. D )
  assume xpcco1st.b: |- B = ( Base ` T )
  assume xpcco1st.k: |- K = ( Hom ` T )
  assume xpcco1st.o: |- O = ( comp ` T )
  assume xpcco1st.x: |- ( ph -> X e. B )
  assume xpcco1st.y: |- ( ph -> Y e. B )
  assume xpcco1st.z: |- ( ph -> Z e. B )
  assume xpcco1st.f: |- ( ph -> F e. ( X K Y ) )
  assume xpcco1st.g: |- ( ph -> G e. ( Y K Z ) )
  assume xpcco2nd.1: |- .x. = ( comp ` D )


  assert |- ( ph -> ( 2nd ` ( G ( <. X , Y >. O Z ) F ) ) = ( ( 2nd ` G ) ( <. ( 2nd ` X ) , ( 2nd ` Y ) >. .x. ( 2nd ` Z ) ) ( 2nd ` F ) ) )

  proof
    wph
    cG
    cF
    cX
    cY
    cop
    cZ
    cO
    co
    co
    #
    cG
    c1st
    cfv
    #
    cF
    c1st
    cfv
    #
    cX
    c1st
    cfv
    cY
    c1st
    cfv
    cop
    cZ
    c1st
    cfv
    cC
    cco
    cfv
    #
    co
    #
    co
    #
    cG
    c2nd
    cfv
    #
    cF
    c2nd
    cfv
    #
    cX
    c2nd
    cfv
    cY
    c2nd
    cfv
    cop
    cZ
    c2nd
    cfv
    c.x
    co
    #
    co
    #
    cop
    wceq
    @0
    c2nd
    cfv
    @9
    wceq
    wph
    cB
    cC
    cD
    c.x
    cT
    @3
    cF
    cG
    cK
    cO
    cX
    cY
    cZ
    xpcco1st.t
    xpcco1st.b
    xpcco1st.k
    @3
    eqid
    xpcco2nd.1
    xpcco1st.o
    xpcco1st.x
    xpcco1st.y
    xpcco1st.z
    xpcco1st.f
    xpcco1st.g
    xpcco
    @5
    @9
    @0
    @1
    @2
    @4
    ovex
    @6
    @7
    @8
    ovex
    op2ndd
    syl
end
