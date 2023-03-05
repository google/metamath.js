const {descent: {parse, process}, metamath: {MM}} = module;

class Code extends React.Component {
  render() {
    const c = this.props.mm.labels["$c"].map(([, c]) => c).flat();
    
    return (
      <code style={{padding: "0.3em 0.5em"}}>
        {this.props.src.split(" ").map((ch, i) =>
          c.includes(ch) ?
            <b style={{color: "#7928a1", padding: "0.2em", cursor: "pointer"}} title={`${ch} is a declared constant.`} key={i}>{ch}</b> :
            <span key={i} style={{color: "#d91e18", padding: "0.2em", cursor: "pointer"}} title={`${ch} is a declared var.`}>{ch}</span>)}
      </code>
    );
  }
}

class Theorem extends React.Component {
  render() {
    const mm = this.props.mm;

    const statement = mm.labels[this.props.label];
    let [a, [d = [], args = [], hyp = [], [type = "", theorem = []] = []], proof = []] = statement;

    return (
       <div>
         <h1>{a == "$a" ? "Axiom" : "Theorem"} "{this.props.label}"</h1>

         {!statement && (
            <div>
              <img src="/static/loading.gif"></img>
            </div>
         )}
      
         {args.length > 0 && (
           <div>     
             <h2>Arguments</h2>  
             <table>
               <thead>
                 <tr><th>Type</th><th>Name</th></tr>
               </thead>
               <tbody>
               {args.map(([type, name], i) =>
               <tr key={i}>
                 <td><Code mm={mm} src={type}/></td><td><Code mm={mm} src={name}/></td>
               </tr>
               )}
               </tbody>
             </table>
           </div>
         )}

         {hyp.length > 0 && (
           <div>
             <h2>Assumption</h2>  
             <table>
               <thead>
                <tr><th>Label</th><th>Type</th><th>Condition</th></tr>
                </thead>
               <tbody>
               {hyp.map(([sequence, type, label], i) =>
                 <tr key={i}>
                   <td>{label}</td><td><Code mm={mm} src={type}/></td><td><Code mm={mm} src={sequence.join(" ")}/></td>
                 </tr>
               )}
               </tbody>
             </table>
           </div>
         )}

         {theorem.length > 0 && (
            <div>
             <h2>Assertion</h2>
             <table>
               <thead>
                 <tr><th>Type</th><th>Assertion</th></tr>
               </thead>
               <tbody>
               <tr>
                 <td><Code mm={mm} src={type}/></td><td><Code mm={mm} src={theorem.join(" ")}/></td>
               </tr>
               </tbody>
             </table>
           </div>
         )}

        </div>
    );
  }
}

class Window extends React.Component {
  render() {

    if (!this.props.open) {
      return null;
    }
    
    const mm = this.props.mm;

    if (!mm.labels[this.props.open]) {
      return null;
    }
    
    //const open = this.props.open ? this.props.mm.labels[this.props.open] : undefined;
    const open = mm.labels[this.props.open];
    const style = {
      position: "absolute",
      left: "105%",
      width: "80%",
      borderRadius: "6px",
      padding: "0 1em",
      boxShadow:  "0 0 10px rgba(0,0,0,0.3)",
      paddingBottom: "2em",
      bottom: 0,
      overflow: "scroll"
    };
    return (
        <div style={style}>
          {open[0] == "$f" && (
            <React.Fragment>    
              <h1>
                Type Declaration "{this.props.open}"
              </h1>
              <table>
                <thead>
                  <tr><th>Type</th><th>Name</th></tr>
                </thead>
                <tbody>
                  <tr>
                    <td><Code mm={mm} src={open[1][0]} /></td><td><Code mm={mm} src={open[1][1]}/></td>
                  </tr>
                </tbody>
              </table>
            </React.Fragment>
          )}

          {open[0] == "$e" && (
            <React.Fragment>    
              <h1>
                Assumption "{this.props.open}"
              </h1>
              <table>
                <thead>
                  <tr><th>Type</th><th>Name</th></tr>
                </thead>
                <tbody>
                  <tr>
                    <td><Code mm={mm} src={open[1][0]}/></td><td><Code mm={mm} src={open[1][1].join(" ")}/></td>
                  </tr>
                </tbody>
              </table>
            </React.Fragment>  
          )}

          {(open[0] == "$a" || open[0] == "$p") && (
            <Theorem mm={mm} label={this.props.open}></Theorem>
          )}

        </div>
    );
  }
}

class Proof extends React.Component {
  constructor(props) {
    super(props);
    this.state = {};
  }
  render() {
    if (!this.props.proof) {
      return null;
    }
    const mm = this.props.mm;
    const proof = this.props.proof;
    return (
      <div>

        <h2>Proof</h2>

        <div style={{position: "relative", display: "inline-block"}}>
          <table>
            <thead>
              <tr><th>Step</th><th>Rule</th><th>Arguments</th><th>Type</th><th>Expression</th></tr>
            </thead>
            <tbody>
            {proof.map(([step, [type, result], args], i) =>
              <tr key={i}
                style={!this.state.highlight ? {} : (
                  this.state.highlight.includes(i) ? {} : {opacity: 0.1, backgroundColor: "none"})}
                onMouseEnter={() => this.setState({"highlight": [...args, i], "open": step})}
                onMouseLeave={() => this.setState({"highlight": undefined, "open": undefined})}>
                <td>{i}</td>
                <td>{(mm.labels[step][0] == "$a" || mm.labels[step][0] == "$p") && (
                  <a href={"#" + step} onClick={() => {this.setState({"label": step});}}>{step}</a>
                )}
                {(mm.labels[step][0] != "$a" && mm.labels[step][0] != "$p") && (
                  step
                )}
                </td>
                <td>{args.join(", ")}</td>
                <td><Code mm={mm} src={type}/></td>
                <td><Code mm={mm} src={result.flat().join(" ")}/></td>
                </tr>
              )}
            </tbody>
          </table>
          <Window mm={mm} open={this.state.open}/>
          </div>
        </div>
    );
  }
}

class Metamath extends React.Component {
  constructor(props) {
    super(props);
    const source = this.props.children;
    
    const label = window.location.hash ? window.location.hash.substr(1) : this.props.label;

    // console.log(process);
    
    this.state = {
      source: source,
      mm: process(source),
      label: label,
      open: false,
    };
  }

  async compute() {
    const label = window.location.hash ? window.location.hash.substr(1) : this.props.label;
    this.setState({
      label: label,
      open: false,
    });

    window.scroll({
      top: 0, 
      left: 0, 
      behavior: 'smooth' 
    });
  }
  
  componentDidMount() {
    window.addEventListener('hashchange', this.compute.bind(this), false);
  }

  render() {
    const statement = this.state.mm.labels[this.state.label];
    let [a, [d = [], args = [], hyp = [], [type, theorem] = []], proof = () => []] = statement;

    const hash = window.location.hash;
    const mm = this.state.mm;
    
    return (
      <div>
        {hash && (
          <button onClick={() => history.back()}>Back</button>
        )}
        <Theorem mm={mm} label={this.state.label} />
        <Proof mm={mm} proof={proof()}/>
      </div>
    );
  }
}
